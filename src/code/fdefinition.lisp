;;;; This file contains functions that hack on the global function
;;;; namespace (primarily concerned with SETF functions here). Also,
;;;; function encapsulation and routines that set and return
;;;; definitions disregarding whether they might be encapsulated.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB-IMPL")


;;;; fdefinition (fdefn) objects

(defun make-fdefn (name)
  (make-fdefn name))

;;;; lisp linkage table

(define-load-time-global *fname-table-lock* (sb-thread:make-mutex :name "linker mutex"))
(defun ensure-fname-exists (name)
  (cond #+linker-space ((symbolp name) name) (t (find-or-create-fdefn name))))

#+linker-space
(progn
(define-symbol-macro *fname-table* (extern-alien "lisp_linkage_table" system-area-pointer))
(defun linkage-cell-address (index)
  (sap-int (sap+ *fname-table* (ash index sb-vm:word-shift))))
(defun linkage-table-ref (index)
  (sap-ref-sap *fname-table* (ash index sb-vm:word-shift)))
(define-symbol-macro *next-fname-index* (extern-alien "lisp_linkage_table_n_entries" int))

(defun get-fname-linkage-index (fname)
  (with-system-mutex (*fname-table-lock*)
    (ash (get-lisp-obj-address
          (etypecase fname
            (symbol (%primitive sb-vm::slot fname 'symbol-function
                                sb-vm:symbol-func-slot sb-vm:other-pointer-lowtag))
            (fdefn  (%primitive sb-vm::slot fname 'sb-vm::fdefn-fun
                                sb-vm:fdefn-fun-slot sb-vm:other-pointer-lowtag))))
         (- sb-vm::symbol-function-bits))))

(export 'get-linkage-entry)
(defun get-linkage-entry (fname)
  (let ((index (get-fname-linkage-index (ensure-fname-exists fname))))
    (if (zerop index)
        (values nil nil)
        (let ((value (linkage-table-ref index)))
          (values (sb-di::code-header-from-pc value) value)))))

;;; Assign EXECUTABLE into the linkage table at specifed INDEX,
;;; also indicating that FNAME was touched
(defun set-lisp-linkage-cell (fname index executable)
  (with-pinned-objects (executable)
    ;; Linkage cell logically belongs to FNAME and can create old->young pointer
    ;; (so that linkage space does not need to be considered a GC root)
    (%primitive sb-vm::gc-store-barrier fname)
    (let ((entrypoint
           (sap+ (int-sap (get-lisp-obj-address executable))
                 (etypecase executable
                   (code-component
                    (- (ash 4 sb-vm:word-shift) sb-vm:other-pointer-lowtag))
                   (function
                    ;; Should this read the fun-self word?
                    (- (ash 2 sb-vm:word-shift) sb-vm:fun-pointer-lowtag))))))
    ;; It's essential to give the linkage entry a valid value
    ;; before publishing that the fname has that index.
    ;; Consider the reverse order: someone reads the index, deems it good,
    ;; emits an instruction to call it, invokes that instruction, jumps
    ;; to 0, all before this thread has stored into the table.
    (setf (sap-ref-sap *fname-table* (ash index sb-vm:word-shift))
          entrypoint)))
  (sb-thread:barrier (:write)))

(defun ensure-fname-linkage-index (designator
                                   &aux (fname (if (typep designator '(or symbol fdefn))
                                                   designator
                                                   (find-or-create-fdefn designator))))
  ;; FNAME is either a symbol or an fdefn
  ;; Preserve the FUNCTION part of the function field
  ;; FIXME: compare-and-swap etc
  (with-pinned-objects (fname)
    (let* ((slot-offset
            (etypecase fname
              (symbol (- (ash sb-vm:symbol-func-slot sb-vm:word-shift)
                         sb-vm:other-pointer-lowtag))
              (fdefn (- (ash sb-vm:fdefn-fun-slot sb-vm:word-shift)
                        sb-vm:other-pointer-lowtag))))
           (bits (sap-ref-word (int-sap (get-lisp-obj-address fname)) slot-offset))
           (index (ash bits (- sb-vm::symbol-function-bits)))
           (current-definition
            ;; FIXME: unsafe
            (%make-lisp-obj (ldb (byte sb-vm::symbol-function-bits 0) bits))))
      (unless (zerop index)
        (return-from ensure-fname-linkage-index index))

      ;; outside of acquiring any locks on the fname table,
      ;; make a closure-calling trampoline now if needed.
      (let ((executable
             (cond ((null current-definition) (error "can't happen"))
                   ((eql current-definition 0) (sb-vm:make-trampoline fname))
                   ((closurep current-definition) (sb-vm:make-trampoline current-definition))
                   (t current-definition))))
        (with-pinned-objects (executable)
          (with-system-mutex (*fname-table-lock*)
            ;; FIXME: double-check that index is zero
            ;; Choose the table index
            (setq index *next-fname-index*
                  *next-fname-index* (1+ index))
            (set-lisp-linkage-cell fname index executable)
            ;; Now that the fname linker table contains a directly callable
            ;; entry point it is safe to assign the table index into the FNAME.
            (setf (sap-ref-word (int-sap (get-lisp-obj-address fname)) slot-offset)
                  (logior (ash index sb-vm::symbol-function-bits)
                          (get-lisp-obj-address current-definition))))))
      index)))

(defun set-fname-function (fname function)
  ;; FNAME is either a symbol or an fdefn
  ;; Preserve the linker-index part of the function field
  ;; And install a trampoline if we need it.
  (declare (type (or function (eql 0)) function))
  (with-pinned-objects (fname function)
    (with-system-mutex (*fname-table-lock*)
      (let* ((slot-offset
              (etypecase fname
                (symbol (- (ash sb-vm:symbol-func-slot sb-vm:word-shift) sb-vm:other-pointer-lowtag))
                (fdefn  (- (ash sb-vm:fdefn-fun-slot sb-vm:word-shift) sb-vm:other-pointer-lowtag))))
             (old (sap-ref-word (int-sap (get-lisp-obj-address fname)) slot-offset))
             (index (ash old (- sb-vm::symbol-function-bits)))
             (new (dpb (get-lisp-obj-address function) (byte sb-vm::symbol-function-bits 0) old))
             (executable
              (when (plusp index)
                (cond ((eql function 0) (sb-vm:make-trampoline fname))
                      ((closurep function) (sb-vm:make-trampoline function))
                      (t function)))))
        (%primitive sb-vm::gc-store-barrier fname)
        (when (plusp index)
          (set-lisp-linkage-cell fname index executable))
        (typecase fname
          (symbol (%primitive sb-vm::set-slot fname (%make-lisp-obj new) '(setf symbol-function)
                              sb-vm:symbol-func-slot sb-vm:other-pointer-lowtag))
          (fdefn
           (%primitive sb-vm::set-slot fname (%make-lisp-obj new) '(setf fdefinition)
                       sb-vm:fdefn-fun-slot sb-vm:other-pointer-lowtag))))))
  function)
) ; end PROGN

#-linker-space
(defun (setf fdefn-fun) (fun fdefn)
  (declare (type function fun)
           (type fdefn fdefn)
           (values function))
  (setf (fdefn-fun fdefn) fun))

;;;;

;;; Return the FDEFN object for NAME, or NIL if there is no fdefn.
;;; Signal an error if name isn't valid.
;;; Assume that exists-p implies LEGAL-FUN-NAME-P.
;;; If #+linker-space then FDEFNs can only be created for names that aren't symbols.
(declaim (ftype (sfunction ((or cons #-linker-space symbol)) (or fdefn null)) find-fdefn))
(defun find-fdefn (name)
  (declare (explicit-check))
  #+linker-space (aver (not (symbolp name)))
  #-linker-space
  (when (symbolp name) ; Don't need LEGAL-FUN-NAME-P check
    (let ((fdefn (sb-vm::%symbol-fdefn name))) ; slot default is 0, not NIL
      (return-from find-fdefn (if (eql fdefn 0) nil fdefn))))
  ;; Technically the ALLOW-ATOM argument of NIL isn't needed, but
  ;; the compiler isn't figuring out not to test SYMBOLP twice in a row.
  (with-globaldb-name (key1 key2 nil) name
      :hairy
      (awhen (get-fancily-named-fdefn name nil)
        (return-from find-fdefn it))
      :simple
      (progn
        (awhen (symbol-dbinfo key1)
          (multiple-value-bind (data-idx descriptor-idx field-idx)
              (info-find-aux-key/packed it key2)
            (declare (type index descriptor-idx)
                     (type (integer 0 #.+infos-per-word+) field-idx))
          ;; Secondary names must have at least one info, so if a descriptor
          ;; exists, there's no need to extract the n-infos field.
            (when data-idx
              (when (eql (incf field-idx) +infos-per-word+)
                (setq field-idx 0 descriptor-idx (1+ descriptor-idx)))
              (when (eql (packed-info-field it descriptor-idx field-idx)
                         +fdefn-info-num+)
                (return-from find-fdefn
                  (%info-ref it (1- (the index data-idx))))))))
        (when (eq key1 'setf) ; bypass the legality test
          (return-from find-fdefn nil))))
  (legal-fun-name-or-type-error name))

;;; Return T if FUNCTION is the error-signaling trampoline for a macro or a
;;; special operator. Test for this by seeing whether FUNCTION is the same
;;; closure as for a known macro.
(declaim (inline macro/special-guard-fun-p))
(defun macro/special-guard-fun-p (function)
  ;; When inlined, this is a few instructions shorter than CLOSUREP
  ;; if we already know that FUNCTION is a function.
  ;; It will signal a type error if not, which is the right thing to do anyway.
  ;; (this isn't quite a true predicate)
  (and (= (%fun-pointer-widetag function) sb-vm:closure-widetag)
       ;; This test needs to reference the name of any macro, but in order for
       ;; cold-init to work, the macro has to be defined first.
       ;; So pick DX-LET, as it's in primordial-extensions.
       ;; Prior to cold-init fixing up the load-time-value, this compares
       ;; %closure-fun to 0, which is ok - it returns NIL.
       (eq (load-time-value (%closure-fun (symbol-function 'dx-let)) t)
           (%closure-fun function))))

;;; This is the implementation of (COERCE s 'function) when S is of type symbol
;;; used by either the full call or the compile-time transform for that pattern.
(defun coerce-symbol-to-fun (symbol)
  (let ((def (%symbol-function symbol)))
    (cond ((not def) (error 'undefined-function :name symbol))
          ((macro/special-guard-fun-p def)
           (error (ecase (car (%fun-name def))
                    (:macro "~S names a macro.")
                    (:special "~S names a special operator."))
                  symbol))
          (t def))))

(declaim (ftype (sfunction ((or cons #-linker-space symbol)) fdefn) find-or-create-fdefn))
(defun find-or-create-fdefn (name)
  (cond
    ((symbolp name)
     #+linker-space (find-fdefn name) ; will signal error
     #-linker-space
     (let ((fdefn (sb-vm::%symbol-fdefn name)))
       (if (eql fdefn 0)
           (let* ((new (make-fdefn name))
                  (actual (sb-vm::cas-symbol-fdefn name 0 new)))
             (if (eql actual 0) new (the fdefn actual)))
           fdefn)))
    ((find-fdefn name))
    (t
      ;; We won't reach here if the name was not legal
      (let (made-new)
        (dx-flet ((new (name)
                    (setq made-new t)
                    (make-fdefn name)))
          (let ((fdefn (with-globaldb-name (key1 key2) name
                        :simple (get-info-value-initializing
                                 :function :definition name (new name))
                        :hairy (get-fancily-named-fdefn name #'new))))
            ;; Slot accessors spring into existence as soon as a reference
            ;; is made to the respective fdefn, but we can't do this in
            ;; (flet NEW) because ENSURE-ACCESSOR calls (SETF FDEFINITION)
            ;; which would recurse, as the fdefn would not have been
            ;; installed yet.
            (when (and made-new
                       (typep name '(cons (eql sb-pcl::slot-accessor))))
              (sb-pcl::ensure-accessor name))
            fdefn))))))

;;; Remove NAME's FTYPE information unless it was explicitly PROCLAIMED.
;;; The NEW-FUNCTION argument is presently unused, but could be used
;;; for checking compatibility of the NEW-FUNCTION against a proclamation.
;;; (We could issue a warning and/or remove the type if incompatible.)
(defun maybe-clobber-ftype (name new-function)
  (declare (ignore new-function))
  ;; Ignore PCL-internal function names.
  (unless (pcl-methodfn-name-p name)
    (unless (eq :declared (info :function :where-from name))
      (clear-info :function :type name))))

;;; Return the fdefn-fun of NAME's fdefinition including any
;;; encapsulations.  This is the core of the implementation of the standard
;;; FDEFINITION function, but as we've defined FDEFINITION, that
;;; strips encapsulations.
(defun %coerce-name-to-fun (name)
  (typecase name
    ((and symbol (not null))
     (let ((fun (%symbol-function name)))
       (when (and fun (not (macro/special-guard-fun-p fun)))
         (return-from %coerce-name-to-fun fun))))
    (cons
     (binding* ((fdefn (find-fdefn name) :exit-if-null)
                (fun (fdefn-fun fdefn) :exit-if-null))
       (return-from %coerce-name-to-fun fun))))
  ;; We explicitly allow any function name when retrying,
  ;; even if the erring caller was SYMBOL-FUNCTION. It is consistent
  ;; that both #'(SETF MYNEWFUN) and '(SETF MYNEWFUN) are permitted
  ;; as the object to use in the USE-VALUE restart.
  (setq name (restart-case (if (legal-fun-name-p name)
                               (error 'undefined-function :name name)
                               (legal-fun-name-or-type-error name))
               (continue ()
                 :report (lambda (stream)
                           (format stream "Retry using ~s." name))
                 name)
               (use-value (value)
                 :report (lambda (stream)
                           (format stream "Use specified function"))
                 :interactive read-evaluated-form
                 (if (functionp value)
                     (return-from %coerce-name-to-fun value)
                     value))))
  (%coerce-name-to-fun name))

;; Coerce CALLABLE (a function-designator) to a FUNCTION.
;; The compiler emits this when someone tries to FUNCALL something.
;; Extended-function-designators are not accepted,
;; This function declares EXPLICIT-CHECK, and we avoid calling
;; SYMBOL-FUNCTION because that would do another check.
;; It would be great if this could change its error message
;; depending on the input to either:
;;   "foo is not a function designator" if not a CALLABLE
;;   "foo does not designate a currently defined function"
;;    if a symbol does not satisfy FBOUNDP.
(defun %coerce-callable-to-fun (callable)
  (declare (explicit-check))
  (typecase callable
    (function
     (return-from %coerce-callable-to-fun callable))
    ((and symbol (not null)) ; NIL can't be fboundp. Quicker test this way.
     (let ((fun (%symbol-function callable)))
       (when (and fun (not (macro/special-guard-fun-p fun)))
         (return-from %coerce-callable-to-fun fun))))
    ;; If NIL, it's not technically a type-error, so instead hit the error
    ;; in %coerce-name-to-fun which has a restart.
    (null)
    (t (error 'type-error :expected-type '(or symbol function) :datum callable)))
  (%coerce-name-to-fun callable))

;;; Behaves just like %COERCE-CALLABLE-TO-FUN but has an ir2-convert optimizer.
(setf (symbol-function '%coerce-callable-for-call) (symbol-function '%coerce-callable-to-fun))


;;;; definition encapsulation

(defstruct (encapsulation-info (:constructor make-encapsulation-info
                                             (type definition))
                               (:copier nil))
  ;; This is definition's encapsulation type. The encapsulated
  ;; definition is in the previous ENCAPSULATION-INFO element or
  ;; installed as the global definition of some function name.
  type
  ;; the previous, encapsulated definition. This used to be installed
  ;; as a global definition for some function name, but it was
  ;; replaced by an encapsulation of type TYPE.
  (definition nil :type function))
(declaim (freeze-type encapsulation-info))

;;; Replace the definition of NAME with a function that calls FUNCTION
;;; with the original function and its arguments.
;;; TYPE is whatever you would like to associate with this
;;; encapsulation for identification in case you need multiple
;;; encapsulations of the same name.
(defun encapsulate (name type function)
  (let ((underlying-fun (%coerce-name-to-fun name)))
    (when (macro/special-guard-fun-p underlying-fun)
      (error "~S can not be encapsulated" name))
    (when (typep underlying-fun 'generic-function)
      (return-from encapsulate
        (encapsulate-generic-function underlying-fun type function)))
    ;; We must bind and close over INFO. Consider the case where we
    ;; encapsulate (the second) an encapsulated (the first)
    ;; definition, and later someone unencapsulates the encapsulated
    ;; (first) definition. We don't want our encapsulation (second) to
    ;; bind basic-definition to the encapsulated (first) definition
    ;; when it no longer exists. When unencapsulating, we make sure to
    ;; clobber the appropriate INFO structure to allow
    ;; basic-definition to be bound to the next definition instead of
    ;; an encapsulation that no longer exists.
    (let ((info (make-encapsulation-info type underlying-fun)))
      (set-fname-function name
            (named-lambda encapsulation (&rest args)
              (apply function (encapsulation-info-definition info)
                     args))))))

;;; Find the encapsulation info that has been closed over.
(defun encapsulation-info (fun)
  (when (closurep fun)
    (find-if-in-closure #'encapsulation-info-p fun)))

;;; When removing an encapsulation, we must remember that
;;; encapsulating definitions close over a reference to the
;;; ENCAPSULATION-INFO that describes the encapsulating definition.
;;; When you find an info with the target type, the previous info in
;;; the chain has the ensulating definition of that type. We take the
;;; encapsulated definition from the info with the target type, and we
;;; store it in the previous info structure whose encapsulating
;;; definition it describes looks to this previous info structure for
;;; a definition to bind (see ENCAPSULATE). When removing the first
;;; info structure, we do something conceptually equal, but
;;; mechanically it is different.
(defun unencapsulate (name type)
  "Removes NAME's most recent encapsulation of the specified TYPE."
  (let* ((fdefn (find-fdefn name))
         (encap-info (encapsulation-info (fdefn-fun fdefn))))
    (declare (type (or encapsulation-info null) encap-info))
    (when (and fdefn (typep (fdefn-fun fdefn) 'generic-function))
      (return-from unencapsulate
        (unencapsulate-generic-function (fdefn-fun fdefn) type)))
    (cond ((not encap-info)
           ;; It disappeared on us, so don't worry about it.
           )
          ((eq (encapsulation-info-type encap-info) type)
           ;; It's the first one, so change the fdefn object.
           (setf (fdefn-fun fdefn)
                 (encapsulation-info-definition encap-info)))
          (t
           ;; It must be an interior one, so find it.
           (loop
             (let ((next-info (encapsulation-info
                               (encapsulation-info-definition encap-info))))
               (unless next-info
                 ;; Not there, so don't worry about it.
                 (return))
               (when (eq (encapsulation-info-type next-info) type)
                 ;; This is it, so unlink us.
                 (setf (encapsulation-info-definition encap-info)
                       (encapsulation-info-definition next-info))
                 (return))
               (setf encap-info next-info))))))
  t)

;;; Does NAME have an encapsulation of the given TYPE?
(defun encapsulated-p (name type)
  (let ((fdefn (find-fdefn name)))
    (when (and fdefn (typep (fdefn-fun fdefn) 'generic-function))
      (return-from encapsulated-p
        (encapsulated-generic-function-p (fdefn-fun fdefn) type)))
    (do ((encap-info (encapsulation-info (fdefn-fun fdefn))
                     (encapsulation-info
                      (encapsulation-info-definition encap-info))))
        ((null encap-info) nil)
      (declare (type (or encapsulation-info null) encap-info))
      (when (eq (encapsulation-info-type encap-info) type)
        (return t)))))

;;;; FDEFINITION

;;; KLUDGE: Er, it looks as though this means that
;;;    (FUNCALL (FDEFINITION 'FOO))
;;; doesn't do the same thing as
;;;    (FUNCALL 'FOO),
;;; and (SYMBOL-FUNCTION 'FOO) isn't in general the same thing
;;; as (FDEFINITION 'FOO). That doesn't look like ANSI behavior to me.
;;; Look e.g. at the ANSI definition of TRACE: "Whenever a traced
;;; function is invoked, information about the call, ..". Try this:
;;;   (DEFUN FOO () (PRINT "foo"))
;;;   (TRACE FOO)
;;;   (FUNCALL 'FOO)
;;;   (FUNCALL (FDEFINITION 'FOO))
;;; What to do? ANSI says TRACE "Might change the definitions of the
;;; functions named by function-names." Might it be OK to just get
;;; punt all this encapsulation stuff and go back to a simple but
;;; correct implementation of TRACE? We'd lose the ability to redefine
;;; a TRACEd function and keep the trace in place, but that seems
;;; tolerable to me. (Is the wrapper stuff needed for anything else
;;; besides TRACE?)
;;;
;;; The only problem I can see with not having a wrapper: If tracing
;;; EQ, EQL, EQUAL, or EQUALP causes its function address to change,
;;; it will mess up the MAKE-HASH-TABLE logic which uses EQ tests
;;; on those function values. But given the ANSI statement about
;;; TRACE causing things to change, that doesn't seem too unreasonable;
;;; and we might even be able to forbid tracing these functions.
;;; -- WHN 2001-11-02
(defun fdefinition (name)
  "Return name's global function definition taking care to respect any
   encapsulations and to return the innermost encapsulated definition.
   This is SETF'able."
  (declare (explicit-check))
  ;; %COERCE-NAME-TO-FUN signals an error for macros and special operators,
  ;; but FDEFINITION should not, so pick off symbols using %SYMBOL-FUNCTION.
  (strip-encapsulation (or (and (symbolp name) (%symbol-function name))
                           (%coerce-name-to-fun name))))
(defun strip-encapsulation (fun)
    (loop
     (let ((encap-info (encapsulation-info fun)))
       (if encap-info
           (setf fun (encapsulation-info-definition encap-info))
           (return fun)))))

(define-load-time-global *setf-fdefinition-hook* nil
  "A list of functions that (SETF FDEFINITION) invokes before storing the
   new value. The functions take the function name and the new value.")

;; Reject any "object of implementation-dependent nature" that
;; so happens to be a function in SBCL, but which must not be
;; bound to a function-name by way of (SETF FEDFINITION).
(defun err-if-unacceptable-function (object setter)
  (when (macro/special-guard-fun-p object)
    (error 'simple-reference-error
           :references '((:ansi-cl :function fdefinition))
           :format-control "~S is not acceptable to ~S."
           :format-arguments (list object setter))))

(defmacro fname-fun (x)
  ;; If #+linker-space, an FNAME is (OR SYMBOL FDEFN), otherwise just FDEFN
  #+linker-space `(if (symbolp ,x) (%symbol-function ,x) (fdefn-fun ,x))
  #-linker-space `(fdefn-fun ,x))

(defun (setf fdefinition) (new-value name)
  "Set NAME's global function definition."
  (declare (type function new-value) (optimize (safety 1)))
  (declare (explicit-check))
  (err-if-unacceptable-function new-value '(setf fdefinition))
  (setq new-value (strip-encapsulation new-value))
  (with-single-package-locked-error (:symbol name "setting fdefinition of ~A")
    (maybe-clobber-ftype name new-value)
    ;; Check for hash-table stuff. Woe onto him that mixes encapsulation
    ;; with this.
    (when (symbolp name)
      (let ((old (%symbol-function name)))
        (dolist (spec *user-hash-table-tests*)
            (cond ((eq old (second spec))
                   ;; test-function
                   (setf (second spec) new-value))
                  ((eq old (third spec))
                   ;; hash-function
                   (setf (third spec) new-value))))))

    (let ((fname (if (or #+linker-space (symbolp name)) name (find-or-create-fdefn name))))
      (dolist (f *setf-fdefinition-hook*)
        (declare (type function f))
        (funcall f name new-value))
      (let ((encap-info (encapsulation-info (fname-fun fname))))
        (cond (encap-info
               (loop
                (let ((more-info
                       (encapsulation-info
                        (encapsulation-info-definition encap-info))))
                  (if more-info
                      (setf encap-info more-info)
                      (return (setf (encapsulation-info-definition encap-info)
                                    new-value))))))
              (t
               #-linker-space (setf (fdefn-fun fname) new-value)
               #+linker-space (set-fname-function fname new-value)))))
    new-value))

;;;; FBOUNDP and FMAKUNBOUND

(defun fboundp (name)
  "Return true if name has a global function definition."
  (declare (explicit-check))
  (acond #+linker-space
         ((typep name '(and symbol (not null)))
          ;; un-fboundp symbols have 0, not NIL in the field
          (let ((f (%primitive sb-vm::fast-symbol-function name))) (if (eql f 0) nil f)))
         ((null name) nil)
         ((find-fdefn name) (fdefn-fun it))))

(defun fmakunbound (name)
  "Make NAME have no global function definition."
  (declare (explicit-check))
  (with-single-package-locked-error
      (:symbol name "removing the function or macro definition of ~A")
    (acond #+linker-space ((symbolp name) (set-fname-function name 0))
           ((find-fdefn name) #+linker-space (set-fname-function it 0)
                              #-linker-space (fdefn-makunbound it)))
    (undefine-fun-name name)
    name))

;;; A simple open-addressing hashset.
(define-load-time-global *fdefns*
  (cons (make-array 128 :initial-element 0) 0))
(define-load-time-global *fdefns-lock* (sb-thread:make-mutex :name "fdefns"))

;;; Fancily named fdefns are not attached to symbols, but instead in a custom
;;; data structure which we probe in the manner of a quadratic probing hash-table.
;;; A max load factor ensures that probing terminates.
;;; https://fgiesen.wordpress.com/2015/02/22/triangular-numbers-mod-2n/
;;; contains a proof that triangular numbers mod 2^N visit every cell.

;;; The intent here - which may be impossible to realize - was to allow garbage-collection
;;; of FDEFNs whose name is not reachable.  I couldn't get it to do the right thing.
;;; e.g. (defmethod foo (x (y cons)) ...) creates mappings:
;;; (SB-PCL::FAST-METHOD FOO (T CONS)) -> #<SB-KERNEL:FDEFN (SB-PCL::FAST-METHOD FOO (T CONS))>
;;; (SB-PCL::SLOW-METHOD FOO (T CONS)) -> #<SB-KERNEL:FDEFN (SB-PCL::SLOW-METHOD FOO (T CONS))>
;;; where it seems like (unintern 'FOO) should allow both of those to get GCd.
;;; I suspect that it will require hanging those fancily named fdefns off the symbol
;;; FOO rather than having a global table.  Alternatively, that can be simulated by
;;; having GC preserve liveness of any element whenever the second item in the list
;;; comprising fdefn-name is an a-priori live symbol.  That will be more efficient than
;;; having a hash-table hanging off every symbol that names a method.
;;; e.g. both of the preceding names would be hanging off of FOO, as would others
;;; such as (FAST-METHOD FOO :AROUND (LIST INTEGER)) and a myriad of others.
;;; I suspect that any approach of hanging off the symbols will be space-inefficient
;;; and difficult to implement.

;;; At any rate, we can make use of the key-in-value nature of fdefns to halve
;;; the number of words required to store the name -> object mapping.
(defun get-fancily-named-fdefn (name constructor &aux (hash (globaldb-sxhashoid name)))
  (declare (type (or function null) constructor))
  (labels ((lookup (vector &aux (mask (1- (length vector)))
                                (index (logand hash mask))
                                (step 0)
                                (empty-cell nil))
             ;; Because rehash is forced well before the table becomes 100% full,
             ;; it should not be possible to loop infinitely here.
             (loop (let ((fdefn (svref vector index)))
                     (cond ((eql fdefn 0) ; not found
                            (return-from lookup (or empty-cell index)))
                           #+nil ((eql fdefn nil) ; smashed by GC
                                  (unless empty-cell (setq empty-cell index)))
                           ((equal (fdefn-name fdefn) name)
                            (return-from lookup fdefn))))
                   (setq index (logand (+ index (incf step)) mask))))
           (insert (hash item vector mask &aux (index (logand hash mask))
                                               (step 0)
                                               (empty-cell nil))
             (loop (case (svref vector index)
                    ((0) ; not found
                     (return (setf (svref vector (or empty-cell index)) item)))
                    #+nil ((nil) ; smashed by GC
                           (unless empty-cell (setq empty-cell index))))
                   (setq index (logand (+ index (incf step)) mask)))))
    (or (let ((result (lookup (car *fdefns*))))
          (when (fdefn-p result) result))
        (when constructor ; double-check w/lock before inserting
          (with-system-mutex (*fdefns-lock*)
            (let* ((fdefns *fdefns*)
                   (vector (car fdefns))
                   (result (lookup vector)))
              (if (fdefn-p result)
                  result
                  (let ((new-fdefn (funcall constructor name)))
                    (if (<= (incf (cdr fdefns)) (ash (length vector) -1)) ; under 50% full
                        ;; It might even be less full than that due to GC.
                        (setf (svref vector result) new-fdefn)
                        ;; The actual count is unknown without re-counting.
                        (let* ((count (count-if #'fdefn-p vector))
                               (new-size (power-of-two-ceiling
                                          (ceiling (* count 2))))
                               (new-vect (make-array new-size :initial-element 0))
                               (new-mask (1- new-size)))
                          (dovector (item vector)
                            (when (fdefn-p item)
                              (insert (globaldb-sxhashoid (fdefn-name item)) item
                                      new-vect new-mask)))
                          (insert hash new-fdefn new-vect new-mask)
                          (setf *fdefns* (cons new-vect (1+ count)))))
                    new-fdefn))))))))

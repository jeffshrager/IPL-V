;;; (load (compile-file "iplv.lisp"))

;;; Things not implemented: Aux storage.

(declaim (optimize (debug 3) (safety 3) (speed 0) (space 0) (compilation-speed 0)))

(defstruct (card (:print-function print-card)) comments type name sign pq symb link comments.1 id)

(defun print-card (card s d)
  (declare (ignore d))
  (format s "~a::~a/~a/~a/~a [~a/~a]"
	  (card-id card)
	  (card-name card)
	  (card-pq card)
	  (card-symb card)
	  (card-link card)
	  (card-comments card)
	  (card-comments.1 card)
	  ))

;;; ===================================================================
;;; Symbol Table (and Stacks)
;;; ===================================================================

(defvar *symtbl* (make-hash-table :test #'equal))

;;; Symbol is a short hand for getting symbol values from the *symtbl* (FFF
;;; Think about using the lisp symbol table instead of *symtbl*. Collisions are
;;; extremely unlikely with everything called W0, M13, and J123! :-)

(defmacro symval (symb) `(gethash ,symb *symtbl*))

;;; *val is symbol value for stacked symbols, like H0 and W0, used where there
;;; isn't a special macro for common ones.  WWW Note the convention of adding +
;;; when the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot try to
;;; push/pop things that aren't stacks!

(defmacro *val+ (symb) `(gethash ,symb *symtbl*)) ;; + Version gets the whole stack
(defmacro *val (symb) `(car (*val+ ,symb)))

;;; Beacuse H0 is so important it has special macros.

(defmacro h0+ () `(*val+ "h0"))
(defmacro h0 () `(*val "h0"))
(defmacro h1+ () `(*val+ "h1"))
(defmacro h1 () `(*val "h1"))
(defmacro h5 () `(*val "h5"))

;;; ===================================================================
;;; The Loader simply loads everything created by tsv2alist.py
;;; into *symtab*. Nb. You should end with a type 5 card to execute!
;;; ===================================================================

(defvar *ipl-trace-list* nil) ;; t for all, or: :load :run 

(defun ipl-trace (key fmt &rest args)
  ;; WWW if the arg is actually nil, apply gets confused so we pre-fix this case.
  (unless args (setf args '(())))
  (when (or (equal *ipl-trace-list* t)
	    (equal key t)
	    (member key *ipl-trace-list*))
    (apply #'format t fmt args)
    (when (member :run-full *ipl-trace-list*)
      (report-important-registers))))

(defparameter *important-run-registers* '("h1" "h0" "h5"))

(defun report-important-registers ()
  (format t "~%***** RUN REGISTERS *****~%")
  (loop for r in *important-run-registers*
	do (format t "  ~a* = ~s~%" r (*val+ r)))
  (format t "^^^^^^^^^^^^^^^^^^^^^^^^^~%")
  )

(defvar *col->vals* (make-hash-table :test #'equal))
(defparameter *cols* '(:comments :type :name :sign :pq :symb :link :comments.1 :id))

(defun load-ipl (file &key (reset? t))
  (when reset? (reset!))
  (with-open-file
      (i file)
    (ipl-trace :load "Loading IPL file: ~a~%" file)
    ;; First line is assumed to be the header which we just check
    (if (equal *cols* (read i))
	(ipl-trace :load "Header okay!~%")
	(error "No valid header on ~a" file)
	)
    (loop for read-row = (read i nil nil)
	  with gather = nil
	  until (null read-row)
	  do
	  (labels ((save-gather ()
		     (when gather
		       (setf gather (reverse gather))
		       (setf (gethash (card-name (car gather)) *symtbl*) gather)
		       (ipl-trace :load "Saved: ~a~%" (card-name (car gather)))
		       (setf gather nil))))
	    (let* ((p -1)
		   (card (make-card
			  :comments (nth (incf p) read-row)
			  :type (nth (incf p) read-row)
			  :name (nth (incf p) read-row)
			  :sign (nth (incf p) read-row)
			  :pq (nth (incf p) read-row)
			  :symb (nth (incf p) read-row)
			  :link (nth (incf p) read-row)
			  :comments.1 (nth (incf p) read-row)
			  :id (nth (incf p) read-row)
			  ))
		   (name (card-name card))
	       	   )
	      (loop for col in *cols* as val in read-row
		    unless (string-equal "" val)
		    do (push val (gethash col *col->vals*)))
	      (cond ((string-equal "" (card-type card))
		     (when (global-symb? name)
		       (ipl-trace :load "Loading global name: ~a~%" name)
		       (save-gather))
	      	     (push card gather))
		    ((and (string-equal "5" (card-type card))
			  (global-symb? (card-symb card)))
		     (format t "*** Execution start at ~a ***~%" (card-symb card))
		     (save-gather)
		     (run (card-symb card)))
		    (t (ipl-trace :load "Ignoring: ~s~%" read-row)))))
	  finally (save-gather)
	  )))


;;; Things like 9-xxx are local, everything else is global.

(defun global-symb? (name)
  (and (not (zerop (length name)))
       (not (char-equal #\9 (aref name 0)))))

(defun reset! ()
  (clrhash *symtbl*) 
  (setup-j-fns)
  (clrhash *col->vals*)
  )

;;; Loaded code analysis:

(defun report-col-vals ()
  (loop for col being the hash-keys of *col->vals*
	using (hash-value vals)
	collect (list col (sort (count-vals vals) #'> :key #'cdr))))

(defvar *val->counts* (make-hash-table :test #'equal))

(defun count-vals (lst)
  (clrhash *val->counts*)
  (dolist (item lst)
    (setf (gethash item *val->counts*) (1+ (gethash item *val->counts* 0))))
  (let (result)
    (maphash (lambda (key value) (push (cons key value) result)) *val->counts*)
    result))

;;; ===================================================================
;;; J-Functions. 
;;; ===================================================================

(eval-when (:execute :load-toplevel :compile-toplevel)
  (defmacro defj (name form)
    `(setf (gethash (string-upcase (format nil "~a" ',name)) *symtbl*)
	   (lambda (arg0 arg1)
	     (ipl-trace :jfns ,(format nil "Calling ~a w/ARG0=~~s, ARG1=~~s~%" name) arg0 arg1)
	     ,form)))
  )

(defun setup-j-fns ()
  (defj J73
      (setf (h0)
	    (copy-list
	     (if (stringp arg0) (*val+ arg0)
		 (if (listp arg0) arg0
		     (error "J73 got ARG0=~s" arg0))))))
  )

;;; ===================================================================
;;; This is the core of the emulator. It directly implements "3.15 THE
;;; INTERPRETATION CYCLE", pg. 164 of the IPL-V manual.
;;; ===================================================================

(defun run (start-symb)
  (prog (h1 card pq q p symb link s)
   START
     (push start-symb (h1+))
     (setf h1 start-symb)
   INTERPRET-Q
     (ipl-trace :run "INTERPRET-Q w/H1 = ~s!~%" h1)
     ;; H1 contains the name of the cell holding the instruction to be
     ;; interpreted. At this point it could be a symbol or a list. If it's a
     ;; symbol, we need to de-reference it to the list. In the case of an
     ;; internal (J) funtion this will be a lambda, in which case we just call
     ;; it and then advance
     (when (stringp h1)
       (ipl-trace :run "~%At INTERPRET-Q: H1 = ~s, de-referencing!~%" h1)
       (setf h1 (*val+ h1) (h1) h1) ;; Set both the var we're using as a shortcut, and the stack entry.
       (go INTERPRET-Q))
     (when (functionp h1)
       (funcall h1 (*val "h0") (cadr (*val+ "h0"))) ;; Call the fn
       (pop (h1+)) ;; Remove the JFn call
       (pop (h1)) ;; And the card that called the JFn
       (print "ccccccc")
       (setf h1 (h1))
       (print "ddddddddd")
       (go ADVANCE))
     (ipl-trace :run "~%H1 = ~s!~%" h1)
     (setq card (car h1))
     (setf pq (card-pq card)
	   q (getpq :q pq)
	   p (getpq :p pq)
	   symb (card-symb card)
	   link (card-link card)
	   )
     (ipl-trace :run "~%At INTERPRET-Q: CARD =~s;" card)
     ;; NNN Note that all the following are separate code segments -- we jump
     ;; around, never passing through to the next section.
     ;; INTERPRET-Q: - Q = 0, 1, 2: Apply Q to SYMBto yield S; go to
     ;; INTERPRET-P.  - Q = 3, 4: Execute monitor action (see ~ 15.0,
     ;; MONITORSYSTEM) ; take S = SYMB; go to INTERPRET-P.  - Q = 5:
     ;; Transfer machine control to SYMB (executing primitive); go to
     ;; ASCEND.  - Q = 6, 7: Bring blocks of routines in from auxiliary
     ;; storage; put location of routine in block into Hl; go to
     ;; INTERPRET-Q.
     (ipl-trace :run " w/Q = ~s~%" q)
     (case q
       (0 (setf s symb) (go INTERPRET-P))
       (1 (setf s (*val symb)) (go INTERPRET-P))
       (2 (setf s (*val (*val symb))) (go INTERPRET-P))
       (3 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" card) (setf s symb) (go INTERPRET-P))
       (4 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" card) (setf s symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go Ascend)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!" card))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!" card))
       )
   INTERPRET-P     
     (ipl-trace :run "INTERPRET-P w/P = ~a~%" p)
     ;; - P = 0: Go to TEST FOR PRIMITIVE. - P=1, 2, 3, 4, 5, 6: Perform the
     ;; - operation; go to  ADVANCE. - P = 7: Go to BRANCH.
     (case p
       (0 (go TEST-FOR-PRIMITIVE))
       (1 ;; Input S (after preserving HO) ;; ??? Hopefully "input" means to push it on the stack ???
	(push s (h0+))
	)
       (2 ;; Output to S (then restore HO)
	(setf s (pop (h0+))))
       (3 ;; Restore (pop up) S
	(pop (*val+ s)))
       (4 ;; Preserve (push down) S
	(push (*val s) (*val s)))
       (5 ;; Replace (0) by S
	(setf (h0) s))
       (6 ;; Copy (0) in S
	(setf (symval s) (h0)))
       (7	     ;; Branch to S if H5-
	(go BRANCH)) ;;; ??? WWW The 3.15 and cheat sheet slightly disagree on this ??? WWW
       )
     (go advance)
   TEST-FOR-PRIMITIVE
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (ipl-trace :run "At TEST-FOR-PRIMITIVE w/S = ~s, Q = ~a~%" s q)
     (case q 
       (5 (setf link (card-symb scard)) (go ADVANCE))
       (t (go DESCEND)))
   ADVANCE
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (card-link card))
     (ipl-trace :run "At ADVANCE w/LINK = ~a~%" link)
     ;; If link is nil ("") in the middle of a function, go next card, else ascend.
     (if (string-equal link "")
	 (if (null h1)
	     (go ASCEND)
	     (progn (setf h1 (cdr h1) (h1) h1) ;; Set both the var we're using as a shortcut, and the stack entry.
		    (go INTERPRET-Q)))
	 (progn
	   (setf h1 link)
	   (go INTERPRET-Q)))
   ASCEND
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (setf h1 (pop (*val+ "h1")) (h1) h1)
     (ipl-trace :run "At ASCEND w/H1 = ~a~%" h1)
     (go ADVANCE)
   DESCEND
     (ipl-trace :run "At DESCEND w/S = ~a~%" s)
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (push s (h1+))
     (setf h1 s)
     (go INTERPRET-Q)
   BRANCH
     (ipl-trace :run "At BRANCH w/H5 = ~a, S= ~a~%" h5 s)
     ;; Interpret Sign in H5: - H5-: Put S as LINK (control transfers to S); go
     ;; to ADVANCE. - HS+: Go to ADVANCE
     (when (not (h5)) (setf link s))
     (go ADVANCE)
     ))

(defun call-ipl-prim (symb)
  (break "****** UNIMPLEMENTED: (call-ipl-prim ~s)" symb))

;;; Getting the P and Q is a little tricky because they can be blank. Blank is
;;; interpreted as zero, and if they're both blank ("") it's not a problem --
;;; both zero, but if only one is blank it can be ambiguous because these didn't
;;; come from cards. This isn't suppose to happen, so if it does, we raise a
;;; warning, and intepret it as if P is blank (0). So, for example, technically
;;; they could have entered "9_" instead of "_9", but we can't tell the
;;; difference. We should always code these as with 90 or 09 to disambiguate.

(defun getpq (pq? val &aux (l (length val)))
  (unless (stringp val) (error "GETPQ was passed VAL = ~s" val))
  (if (> l 2)
      (error "In GETPQ, val = ~s, which shouldn't happen!" val)
      (if (zerop l) 0
	  (if (= 1 l)
	      (case pq? (:p 0) (:q (parse-integer val)))
	      (parse-integer (case pq? (:p (subseq val 0 1)) (:q (subseq val 1 2))))))))

(untrace)
;(trace global-symb? load-ipl ipl-trace)
(setf *ipl-trace-list* '(:run :jfns :run-full))
(load-ipl "runs/20250214/LT.lisp")

;;; (load (compile-file "iplv.lisp"))

********* We've got a little problem here. The system symbols have to be in the symbol
 table too! Fuck!

(defstruct ir comments type name sign pq symb link comments.1 id)

;;; Loader simply loads everything created by tsv2alist.py into
;;; *symtab*

(defvar *stacks* (make-hash-table :test #'equal))
(defvar *symtbl* (make-hash-table :test #'equal))
(defvar *col->vals* (make-hash-table :test #'equal))
(defparameter *cols* '(:comments :type :name :sign :pq :symb :link :comments.1 :id))

(defun global-symb? (name)
  (and (not (zerop (length name)))
       (not (char-equal #\9 (aref name 0)))))

(defun reset! ()
  (clrhash *symtbl*) ;; "ir" == "ipl row"
  (clrhash *col->vals*)
  (clrhash *stacks*)
  )

(defun load-ipl (file &key (reset? t) trace-level)
  (when reset? (reset!))
  (with-open-file
      (i file)
    (format t "Loading IPL file: ~a~%" file)
    ;; First line is assumed to be the header which we just check
    (if (equal *cols* (read i))
	(format t "Header okay!~%")
	(error "No valid header on ~a" file)
	)
    (loop for read-row = (read i nil nil)
	  with gather = nil
	  until (null read-row)
	  do (let* ((p -1)
		    (ir (make-ir
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
		    (name (ir-name ir))
	       	    )
	       (loop for col in *cols* as val in read-row
		     unless (string-equal "" val)
		     do (push val (gethash col *col->vals*)))
	       (cond ((string-equal "" (ir-type ir))
		      (when (global-symb? name)
			(progn 
			  (format t "Loading global name: ~a~%" name)
			  (when gather
			    (setf gather (reverse gather))
			    (setf (gethash (ir-name (car gather)) *symtbl*) gather)
			    (setf gather nil))))
	      	      (push ir gather))
		     ((and (string-equal "5" (ir-type ir))
			   (global-symb? (ir-symb ir)))
		      (format t "*** Execution start at ~a ***~%" (ir-symb ir))
		      (run (ir-symb ir) :trace-level trace-level))
		     (t (format t "Ignoring: ~s~%" read-row))))
	  finally (progn (setf gather (reverse gather))
			 (setf (gethash (ir-name (car gather)) *symtbl*) gather))
	  )))

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

;;; This is based on 3.14-15 of Newell's 1963 IPL-V manual.

;;; Getting the P and Q is a little tricky because they can be blank. Blank is
;;; interpreted as zero, and if they're both blank ("") it's not a problem --
;;; both zero, but if only one is blank it can be ambiguous because these didn't
;;; come from cards. This isn't suppose to happen, so if it does, we raise a
;;; warning, and intepret it as if P is blank (0). So, for example, technically
;;; they could have entered "9_" instead of "_9", but we can't tell the
;;; difference. We should always code these as with 90 or 09 to disambiguate.

(defun getpq (pq? val &aux (l (length val)))
  (if (> l 2)
      (error "In GETPQ, val = ~s, which shouldn't happen!" val)
      (if (zerop l) 0
	  (if (= 1 l)
	      (case pq? (:p 0) (:q (parse-integer val)))
	      (parse-integer (case pq? (:p (subseq val 0 1)) (:q (subseq val 1 2))))))))

;;; Symbol is a short hand for getting symbol values from the *symtbl* (FFF
;;; Think about using the lisp symbol table instead of *symtbl*. Collisions are
;;; extremely unlikely with everything called W0, M13, and J123! :-)

(defmacro symval (symb) `(gethash ,symb *symtbl*))

;;; *val is symbol value for stacked symbols, like H0 and W0, used where there
;;; isn't a special macro for common ones.  WWW Note the convention of adding +
;;; when the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot try to
;;; push/pop things that aren't stacks!

(defmacro *val+ (symb) `(gethash ,symb *stacks*)) ;; + Version gets the whole stack
(defmacro *val (symb) `(car (*val+ ,symb)))

;;; Beacuse H0 is so important it has special macros.

(defmacro h0+ () `(*val "h0"))
(defmacro h0 () `(car (*val "h0")))
(defmacro h1+ () `(*val "h1"))
(defmacro h5 () `(car (*val "h5")))

;;; FFF Think about macrofying the stack ops for common values.

(defun run (h1 &key trace-level)
  (prog (ir pq q p symb link s)
   START
   INTERPRET-Q
     (when trace-level (format t "INTERPRET-Q w/H1 = ~s!~%" h1))
     ;; (setf h1 (*val "h1")) ;; Note that this could be a symbol or a whole list. ????
     ;; H1 contains the name of The cell holding the instruction to be
     ;; interpreted. At this point it could be a symbol or a list. If it's a
     ;; symbol, we need to de-reference it to the list.
     (when (stringp h1)
       (when trace-level (format t "~%At START: H1 = ~s, de-referencing!~%" h1))
       (setf h1 (symval h1)))
     (when trace-level (format t "~%H1 = ~s!~%" h1))
     (setq ir (car h1))
     (setf pq (ir-pq ir)
	   q (getpq :q pq)
	   p (getpq :p pq)
	   symb (ir-symb ir)
	   link (ir-link ir)
	   )
     (when trace-level (format t "~%At INTERPRET-Q: IR =~%~s~%" ir))
     ;; NNN Note that all the following are separate code segments -- we jump
     ;; around, never passing through to the next section.
     ;; INTERPRET-Q: - Q = 0, 1, 2: Apply Q to SYMBto yield S; go to
     ;; INTERPRET-P.  - Q = 3, 4: Execute monitor action (see ~ 15.0,
     ;; MONITORSYSTEM) ; take S = SYMB; go to INTERPRET-P.  - Q = 5:
     ;; Transfer machine control to SYMB (executing primitive); go to
     ;; ASCEND.  - Q = 6, 7: Bring blocks of routines in from auxiliary
     ;; storage; put location of routine in block into Hl; go to
     ;; INTERPRET-Q.
     (when trace-level (format t "  w/Q = ~s~%" q))
     (case q
       (0 (setf s symb) (go INTERPRET-P))
       (1 (setf s (*val symb)) (go INTERPRET-P))
       (2 (setf s (*val (*val symb))) (go INTERPRET-P))
       (3 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" ir) (setf s symb) (go INTERPRET-P))
       (4 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" ir) (setf s symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go Ascend)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!"))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!"))
       )
     (error "Illegal forward pass: INTERPRET-Q to INTERPRET-P!")
   INTERPRET-P     
     (when trace-level (format t "INTERPRET-P w/P = ~a~%" p))
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
     (error "Illegal forward pass: INTERPRET-P to TEST-FOR-PRIMITIVE!")
   TEST-FOR-PRIMITIVE
     (when trace-level (format t "At TEST-FOR-PRIMITIVE w/Q = ~a~%" q))
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (let* ((sir (car (symval s)))
	    (q-of-s (getpq :q (ir-pq sir))))
       (case q-of-s ;; Oh my god, I'm so bored of trying to generalize this!
	 (5 (setf link (ir-symb ir)) (go ADVANCE))
	 (t (go DESCEND))))
     (error "Illegal forward pass: TEST-FOR-PRIMITIVE to ADVANCE!")
   ADVANCE
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (ir-link ir))
     (when trace-level (format t "At ADVANCE w/LINK = ~a~%" link))
     (when (string-equal link "") (go ASCEND))
     (setf h1 link) (go INTERPRET-Q)
     (error "Illegal forward pass: EST-FOR-PRIMITIVE to ADVANCE!")
   ASCEND
     (setf h1 (pop (*v+ "h1"))) ;; ??? Maybe ???
     (when trace-level (format t "At ASCEND w/H1 = ~a~%" h1))
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (go ADVANCE)
     (error "Illegal forward pass: ADVANCE to DESCEND!")
   DESCEND
     (when trace-level (format t "At ASCEND w/S = ~a~%" s))
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (push s (h1+))
     (go INTERPRET-Q)
     (error "Illegal forward pass: DESCEND to BRANCH!")
   BRANCH
     (when trace-level (format t "At BRANCH w/H5 = ~a, S= ~a~%" (h5) s))
     ;; Interpret Sign in H5: - H5-: Put S as LINK (control transfers to S); go
     ;; to ADVANCE. - HS+: Go to ADVANCE
     (when (not (h5)) (setf link s))
     (go ADVANCE)
     (error "Illegal forward pass: BRANCH to exit!")
     ))
    
(untrace)
;(trace global-symb?)
(load-ipl "LT.lisp" :trace-level t)

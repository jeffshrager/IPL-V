;;; (load (compile-file "iplv.lisp"))

(defstruct ir comments type name sign pq symb link comments.1 id)

;;; Loader simply loads everything created by tsv2alist.py into
;;; *symtab*

(defvar *vals* (make-hash-table :test #'equal))
(defvar *symtbl* (make-hash-table :test #'equal))
(defvar *col->vals* (make-hash-table :test #'equal))
(defparameter *cols* '(:comments :type :name :sign :pq :symb :link :comments.1 :id))

(defun global-symb? (name)
  (and (not (zerop (length name)))
       (not (char-equal #\9 (aref name 0)))))

(defun reset! ()
  (clrhash *symtbl*) ;; "ir" == "ipl row"
  (clrhash *col->vals*)
  (clrhash *vals*)
  )

(defun load-ipl (file &key (reset? t))
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
		      (error "Unimplemented: Execution Start!"))
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
	      (case pq? (:p (subseq val 0 1)) (:q (subseq val 1 2)))))))

(defun sv (symb) (car (gethash symb *vals*)))

(defun run (&key trace-level)
  (prog (h0 h1 ir pq q p symb link s)
   START
     (setf h0 (getval :h0)
	   h1 (getval :h1))
     ;; H1 contains the name of The cell holding the instruction to be
     ;; interpreted.  (H1 could be a symbol or the head of a list. If it's a
     ;; symbol, that automatically gets de-ref'ed to the list via the symbol
     ;; table.)
     (when (stringp h1)
       (when trace-level (format t "~%In RUN, at START: H1 = ~s, de-referencing!~%" h1))
       (pushval (getf h1 *symtbl*) :h1)
       (go start))
   DECODE-INSTRUCTION
     (setq ir (car h1))
     (setf pq (ir-pq ir)
	   q (getpq :q pq)
	   p (getpq :p pq)
	   symb (ir-symb ir)
	   link (ir-link ir)
	   )
     (when trace-level (format t "~%In RUN, at DECODE-INSTRUCTION: IR =~%~s~%" ir))
   INTERPRET-Q
     ;; INTERPRET-Q: - Q = 0, 1, 2: Apply Q to SYMBto yield S; go to
     ;; INTERPRET-P.  - Q = 3, 4: Execute monitor action (see ~ 15.0,
     ;; MONITORSYSTEM) ; take S = SYMB; go to INTERPRET-P.  - Q = 5:
     ;; Transfer machine control to SYMB (executing primitive); go to
     ;; ASCEND.  - Q = 6, 7: Bring blocks of routines in from auxiliary
     ;; storage; put location of routine in block into Hl; go to
     ;; INTERPRET-Q.
     (case q
       (0 (setf s symb) (go INTERPRET-P))
       (1 (setf s (first (gethash symb *stacks*))) (go INTERPRET-P))
       (2 (setf s (first (gethash (first (gethash symb *stacks*)) *stacks*))) (go INTERPRET-P))
       (3 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" ir) (setf s symb) (go INTERPRET-P))
       (4 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" ir) (setf s symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go ascend)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!"))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!"))
       )
   INTERPRET-P     
     (break)
     ))
    
(untrace)
;(trace global-symb?)
(load-ipl "LT.lisp")
(mapcar #'print (cadr (assoc :symb (report-col-vals))))



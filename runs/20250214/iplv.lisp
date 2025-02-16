;;; (load (compile-file "iplv.lisp"))

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
  (clrhash *col->vals*))

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

(untrace)
;(trace global-symb?)
(load-ipl "LT.lisp")
(mapcar #'print (cadr (assoc :symb (report-col-vals))))



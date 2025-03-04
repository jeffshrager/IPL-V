;;; (load (compile-file "iplv.lisp"))

#|

To Do (or at least think about):

??? FFF Should W24 (read/print line) be in an actual cell? Right now it's in a
special global that can only process on line of I or O at a time.

FFF Need to find out where the memory leaks are that are leaving junk on the
stacks (primarily H0) -- I think it's the Jfns that aren't cleaning up after
themselves, and/or not absorbing their inputs.

FFF There's a hack for true blanks in both symb and link in LT:/016D070 to avoid
the load-time trap. Eventually, test for data mode 21 to allow both blanks.

|#


;;; WWW Leaves these at high debug etc or things break for unknown reasons.
(declaim (optimize (debug 3) (safety 3) (speed 0) (space 0) (compilation-speed 0)))

;;; ===================================================================
;;; Cell, Storage, and Special Symbols

(defstruct (cell (:print-function print-cell))
  (comments "")
  (type "")
  (name "")
  (sign "")
  (pq "")
  (symb "")
  (link "")
  (comments.1 "")
  (id "")
  )

(defun zero? (what)
  (member (if (stringp what) what
	      (break "ZERO? sent ~s which should be a string or nil." what))
	  '("" "0") :test #'string-equal))

(defun blank? (what)
  (string-equal "" what))

(defun print-cell (cell s d)
  (declare (ignore d))
  (format s "{~a~a/~a/~a/~a~a}"
	  (if (zero? (cell-id cell)) "" (format nil "~a::" (cell-id cell)))
	  (cell-name cell)
	  (cell-pq cell)
	  (cell-symb cell)
	  (cell-link cell)
	  (if (and (zero? (cell-comments cell)) (zero? (cell-comments.1 cell))) 
	      ""
	      (format nil " [~a/~a]" (cell-comments cell) (cell-comments.1 cell)))))

(defvar *trace-instruction* nil) ;; Used in error traps, so need to declare early.
(defvar *fname-hint* "") ;; for messages in the middle of jfn ops

(defvar *symtab* (make-hash-table :test #'equal))

;;; *cell is symbol value for stacked symbols, like H0 and W0, used where there
;;; isn't a special macro for common ones.  WWW Note the convention of adding +
;;; when the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot try to
;;; push/pop things that aren't stacks!

(defmacro cell (symb) `(gethash ,symb *symtab*))
(defmacro stack (symb) `(gethash ,symb *systacks*)) ;; Only system cells have stacks
(defun cell? (cell?) (eq 'cell (type-of cell?)))

;;; Important values it have special macros (these are like (H0) = (0)
;;; in the IPL-V manual). The ...+ fns return the whole stack. (Note
;;; that you'll have to get (1), that is, the second stack entry in H0
;;; manually!)

(defmacro H0 () `(cell "H0"))
(defmacro H0+ () `(stack "H0"))

(defmacro H1 () `(cell "H1")) ;; WWW DO NOT CONFUSE H1 with (1) !!!
(defmacro H1+ () `(stack "H1")) ;; WWW DO NOT CONFUSE H1 with (1) !!!

(defmacro H5 () `(cell "H5"))
(defmacro H5+ () `(stack "H5"))

(defmacro S () `(cell "S"))
(defmacro S+ () `(stack "S"))

(defun ^^ (ssname)
  (trace-cell-or-name? ssname)
  (setf (cell ssname) (pop (stack ssname))))
(defun vv (ssname &optional new-value)
  (trace-cell-or-name? ssname)
  (push (cell ssname) (stack ssname))
  (when new-value (setf (cell ssname) new-value)))

;;; This is a protected version of cell-name that de-refs if necessary.

(defun cell-name% (cell-or-name)
  (cell-name (<== cell-or-name)))

(defun <== (cell-or-name) ;; de-ref-or-die
  (let ((cell (if (cell? cell-or-name) cell-or-name
		  (if (stringp cell-or-name) (cell cell-or-name)))))
    (!! :deep-memory "<== Retreive == ~s = ~s [mem]~%" cell-or-name cell)
    (if (cell? cell) cell
      (break "Trying to deref ~s, which isn't a cell, while executing ~s!" cell-or-name *trace-instruction*))))

(defun new-local-symbol (&optional (prefix "9")) (format nil "~a~a" prefix (gensym "+")))

(defmacro make-cell! (&rest args)
  `(store (make-cell ,@args)))

(defun store (cell &optional (name (cell-name cell)))
  (!! :deep-memory "== Store ==> ~s [mem]~%" cell)
  (trace-cell-or-name? name)
  (setf (gethash name *symtab*) cell)
  cell)
  
;;; This can trace strings, or any element (name/symb/link) of a cell
;;; incl. stackables.

(defvar *running?* nil)

(defun trace-cell-or-name? (cell-or-name)
  (when *running?* 
    (let ((names (if (stringp cell-or-name)
		     (list cell-or-name)
		     (if (cell? cell-or-name)
			 (cell-name (list (cell-name cell-or-name) (cell-symb cell-or-name) (cell-link cell-or-name)))))))
      (when (intersection names *trace-cell-names* :test #'string-equal)
	(format t "======= Tracing ~s: ~s =======~%" (car names) (<== (car names)))
	(when (gethash (car names) *systacks*)
	  (pprint (gethash (car names) *systacks*))
	  (format t "============================~%"))
	))))

(defun store-cells (cells)
  (loop for cell in cells
	as name = (cell-name cell)
	unless (zero? name) ;; Until?
	do (store cell)))

;;; This is used for all IO at the moment, under the assumption (until otherwise
;;; demonstrated wrong) that LT does it's IO one line at a time, full processing
;;; those lines and then clearing the buffer and doing the next.

(defun blank80 () (subseq (format nil "~81d" 0) 0 80))

(defvar *W24-Line-Buffer* (Blank80))

;;; ===================================================================
;;; Debugging Utils

(defvar *trace-cell-names* nil) 
(defvar *!!list* nil) ;; t for all, or: :load :run :run-full

(defun !! (key fmt &rest args)
  ;; WWW if the arg is actually nil, apply gets confused so we pre-fix this case.
  (unless args (setf args '(())))
  (when (or (equal *!!list* t)
	    (equal key t)
	    (member key *!!list*))
    (format t "!![~a]::" key)
    (apply #'format t fmt args)
    (when (and (member key '(:run :run-full)) (member :run-full *!!list*))
      (report-system-cells))))

;;; This also checks to make sure that there isn't crap left on the
;;; stacks or in the cells and breaks if ther is. 

(defun report-system-cells (&optional all?)
  (format t "~%~%------ RUN REGISTERS ------~%")
  (loop for cellname in (if all? *all-system-cells* *system-cells*)
	do (format t "  ~a=~s ~s~%" cellname (cell cellname) (stack cellname)))
  (format t "-----------------------~%~%")
  ;; Check for disasters
  (loop for cellname in *system-cells*
	with warn = nil
	as cell = (cell cellname)
	as stack = (stack cellname)
	do (cond ((illegal-value? cell) (format t "!!!!! ~s contains a zero or blank !!!!!~%" cellname) (setf warn t))
		 ((loop for entry in stack if (illegal-value? entry) do (return t))
		  (format t "!!!!! An entry in ~s's stack is zero or blank !!!!!~%" cellname) (setf warn t))
		 )
	finally (when warn (format t "!!! Illegal cell while executing: ~s :: This shouldn't happen !!!~%" *trace-instruction*))))

(defun illegal-value? (val) ;; Might be other conditions.
  (or (null val) (and (stringp val) (string-equal val ""))))

;;; ===================================================================
;;; Loader (loads from files converted by tsv2lisp.py)

;;; FFF Note that the dumper puts multiple header lines in (:comments :type :name
;;; :sign :pq :symb :link :comments.1 :id). Prob. need code to ignore them
;;; rather than just skipping the first line.

(defvar *col->vals* (make-hash-table :test #'equal))
(defparameter *cols* '(:comments :type :name :sign :pq :symb :link :comments.1 :id))

(defvar *input-stream* nil) 
(defvar *card-number* nil)

(defun load-ipl (file &key (reset? t) (load-mode :code) (adv-limit 100))
  ;; Load-mode will be :code or :data as set by the latest type=5
  ;; cell's Q: Q=0=code, Q=1=data) And if the sym entry on a type 5
  ;; cell is filled, it's an execution start cell.
  (setf *running?* nil) ;; Protect from deep tracing of things that aren't setup yet!
  (when reset? (reset!))
  (with-open-file
      (i file)
    (setf *card-number* 0)
    (setf *input-stream* i) ;; For reads inside the program executor
    (!! :load "Loading IPL file: ~s~%" file)
    ;; First line is assumed to be the header which we just check
    (if (equal *cols* (read i))
	(!! :load "Header okay!~%")
	(error "No valid header on ~s" file)
	)
    (loop for read-row = (read i nil nil)
	  with cells = nil
	  until (null read-row)
	  do (!! :load "Reading card number ~a: ~s~%" (incf *card-number*) read-row)
	  (let* ((p -1)
		 (cell (make-cell
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
		 (name (cell-name cell))
	       	 )
	    ;; Collect frequency of symbol use data.
	    (loop for col in *cols* as val in read-row
		  unless (zero? val)
		  do (push val (gethash col *col->vals*)))
	    (if (zero? (cell-type cell))
		(progn 
		  (when (global-symbol? name)
		    (!! :load "Loading global name: ~s~%" name)
		    (save-cells (reverse cells) load-mode) (setf cells nil))
	      	  (push cell cells))
		(if (string-equal "5" (cell-type cell))
		    (if (global-symbol? (cell-symb cell))
			(progn
			  (!! :run "** Execution start at ~s **~%" (cell-symb cell))
			  (save-cells (reverse cells) load-mode)
			  (setf cells nil)
			  (run (cell-symb cell) :adv-limit adv-limit))
			(if (member (cell-pq cell) '("1" "01") :test #'string-equal)
			    (progn
			      (save-cells (reverse cells) load-mode) (setf cells nil)
			      (!! :load "Switching to DATA load mode.~%")
			      (setf load-mode :data))
			    (if (member (cell-pq cell) '("0" "00" "") :test #'string-equal)
				(progn
				  (!! :load "Switching to CODE load mode.~%")
				  (save-cells (reverse cells) load-mode) (setf cells nil)
				  (setf load-mode :code))
				(!! :load "Ignoring: ~s~%" read-row)))))))
	  finally (save-cells (reverse cells) load-mode)
	  )))

(defparameter *symbol-col-accessors* `((cell-name . ,#'cell-name) (cell-symb . ,#'cell-symb) (cell-link . ,#'cell-link)))

(defun save-cells (cells load-mode)
  ;; Before doing anything else we massage data-type cards (load-mode :data) in
  ;; accord with the PQ.
  (when (eq load-mode :data)
    (loop for cell in cells
	  as pq = (cell-pq cell)
	  do (cond ((member pq '("1" "01") :test #'string-equal)
		    (setf (cell-link cell) (parse-integer (cell-link cell))))
		   ((string-equal pq "11")
		    (break "Floating point is not implemented: ~s" cell))
		   ((string-equal pq "21")) ;; Alpha -- just leave the symb as is
		   ((not (string-equal pq ""))
		    (break "Invalid PQ in ~s" cell)))))
  ;; Once we have the thing completely in hand, we change the local
  ;; symbols to FN_9-... and save those as separate symtab
  ;; entries. This allows the code to branch, and also run through,
  ;; and also use sub sections of code in J100 meta-calls (ugh!) WWW
  ;; !!! This looks like it's duplicative as each sublist contains all
  ;; the sublists after it.  However this is unfortunately required as
  ;; sometimes the code runs through. In load-mode :data we have to
  ;; assign a local symbol to every cell. (Really we could do this in
  ;; every mode since the functions are just lists, but things would
  ;; look extremely messy and the symtab would be totally full of ugly
  ;; crap -- which is, of course, how the actual computer works, where
  ;; core is the symtab! So for the sake of a bit of cleanliness we
  ;; create a spaghetti monster out of the emulator!)
  (when cells
    (let* ((top-name (cell-name (car cells)))
	   (local-symbols.new-names
	    (uniquify-list
	     (loop for cell in cells
		   append (loop for (nil . getter) in *symbol-col-accessors*
				as symbol = (funcall getter cell)
				if (local-symbol? symbol)
				collect (cons symbol (format nil "~a-~a" top-name symbol)))))))
      (convert-local-symbols cells local-symbols.new-names)
      (setf (gethash top-name *symtab*) (car cells)) ;; ?? Can/Should this be a (store ...)
      (!! :load "Saved: ~s~%" (cell-name (car cells)))
      ;; Loop through the whole list and create a local symbol for every cell
      ;; that doesn't already have one. 
      (loop for (this-cell next-cell) on cells
	    as this-symb = (cell-symb this-cell)
	    as this-link = (cell-link this-cell)
	    as next-name = (when next-cell (cell-name next-cell))
	    when next-cell ;; This usually isn't needed anyway bcs there should be a 0
	    do
	    (if (and (blank? this-link) (blank? this-symb))
		(break "Both symb and link can't be blank: ~s!!" this-cell))
	    (if (blank? this-link)
		(if (blank? next-name)
		    (let ((new-symbol (new-local-symbol top-name)))
		      (setf (cell-name next-cell) new-symbol)
		      (setf (cell-link this-cell) new-symbol))
		    (setf (cell-link this-cell) next-name)))
	    (if (blank? this-symb)
		(if (blank? next-name)
		    (let ((new-symbol (new-local-symbol top-name)))
		      (setf (cell-name next-cell) new-symbol)
		      (setf (cell-symb this-cell) new-symbol))
		    (setf (cell-symb this-cell) next-name))))
      (store-cells cells)
      )))

(defun convert-local-symbols (cells local-symbols.new-names)
  (labels ((replace-symbols (cell accname.accessor)
	     (let ((new-name (cdr (assoc (funcall (cdr accname.accessor) cell) local-symbols.new-names :test #'string-equal))))
	       (when new-name (setf* (car accname.accessor) cell new-name)))))
    (loop for cell in cells
	  do (loop for accname.accessor in *symbol-col-accessors*
		   do (replace-symbols cell accname.accessor)))))
			    
;;; This stupidity is needed because setf doesn't know how to set a value based
;;; on an arbitrary accessor.

(defun setf* (accname cell new-name)
  (case accname
    (cell-name (setf (cell-name cell) new-name))
    (cell-symb (setf (cell-symb cell) new-name))
    (cell-link (setf (cell-link cell) new-name))))

;;; Things like 9-xxx are local, everything else is global.

(defun global-symbol? (name)
  (and (not (zerop (length name)))
       (not (char-equal #\9 (aref name 0)))))

(defun local-symbol? (name)
  (if (numberp name) nil
      (and (not (zerop (length name)))
	   (char-equal #\9 (aref name 0)))))

(defun uniquify-list (l)
  (loop for i on l
	unless (member (car i) (cdr i) :test #'equal)
	collect (car i)))

(defvar *jfn-plists* (make-hash-table :test #'equal))

(defun reset! ()
  (clrhash *systacks*)
  (clrhash *symtab*) 
  (setup-j-fns)
  (clrhash *col->vals*)
  )

;;; Note that S and H5 are nots cells but just symbols, but they're
;;; both stackable (protectable), so they need to have stacks.

(defparameter *system-cells* '("H0" "H1" "H3" "H5" "W0" "S"))
(defparameter *all-system-cells* (append *system-cells* (loop for w below 43 collect (format nil "W~a" w))))

(defvar *systacks* (make-hash-table :test #'equal))

(defun create-system-cells ()
  (loop for name in *all-system-cells*
	do
	(make-cell! :name name)
	(setf (gethash name *systacks*) (list (format nil "~a-empty" name)))
	(!! :deep-memory "Created system cell: ~s and its stack.~%" name))
  (setf (cell "S") "S-is-null")
  )

;;; This is needed because of H0 memory leaks, probably from JFNS.
(defvar *stack-depth-limit* 100)

(defun clean-stacks ()
  (when *stack-depth-limit*
    (loop for key being the hash-keys of *systacks*
	  using (hash-value stack)
	  as depth = (length stack)
	  do
	  (when (> depth *stack-depth-limit*)
	    (!! :deep-memory "Tailing stack ~a, now ~a deep, to ~a. [mem]~%" key depth *stack-depth-limit*)
	    (loop for s+ on stack
		  as d below *stack-depth-limit*
		  finally (setf (cdr s+) nil))))))

;;; Loaded code analysis:

(defun report-col-vals ()
  (loop for col being the hash-keys of *col->vals*
	using (hash-value vals)
	collect (list col (sort (count-vals vals) #'> :key #'cdr))))

(defvar *cell->counts* (make-hash-table :test #'equal))

(defun count-vals (lst)
  (clrhash *cell->counts*)
  (dolist (item lst)
    (setf (gethash item *cell->counts*) (1+ (gethash item *cell->counts* 0))))
  (let (result)
    (maphash (lambda (key value) (push (cons key value) result)) *cell->counts*)
    result))

;;; ===================================================================
;;; J-Functions. 

;;; (WWW You's think we could pop the input args off H0 automatically,
;;; but some IPL code leave the input args in place on purpose.)

(defmacro defj (name args explanation &rest forms)
  `(let ((uname ,(string-upcase (format nil "~a" name))))
     (setf (gethash uname *jfn-plists*) '(explanation ,explanation))
     (setf (gethash uname *symtab*)
	   (lambda ,args
	     ,@forms))))

(defun setup-j-fns ()

  (defj J2 (arg0 arg1) "TEST (0) = (1)?" (setf (h5) (if (equal arg0 arg1) "+" "-")))
  (defj J3 () "SET H5 -" (setf (H5) "-"))
  (defj J4 () "SET H5 +" (setf (H5) "+"))

  (defj J6 () "REVERSE (0) and (1)" ;; WWW H1 is not (1)
	(let ((z (H0)))
	  (setf (H0) (first (H0+)))
	  (setf (first (H0+)) z)))

  (defj J8 () "RESTORE H0" (^^ "H0"))

  ;; I don't think that this is necessary as we don't need to do our own GC.
  (defj J9 () "ERASE CELL (0)" (!! :jfns "J9 is a noop as we don't need to do our own GC."))

  ;; FFF Macrofiy these!!!

  (defj J20 () "MOVE(0)-(0) into W0-0" (J2n=move-0-to-n-into-w0-wn 0))
  (defj J21 () "MOVE(0)-(1) into W0-1" (J2n=move-0-to-n-into-w0-wn 1))
  (defj J22 () "MOVE(0)-(2) into W0-2" (J2n=move-0-to-n-into-w0-wn 2))
  (defj J23 () "MOVE(0)-(3) into W0-3" (J2n=move-0-to-n-into-w0-wn 3))
  (defj J24 () "MOVE(0)-(4) into W0-4" (J2n=move-0-to-n-into-w0-wn 4))
  (defj J25 () "MOVE(0)-(5) into W0-5" (J2n=move-0-to-n-into-w0-wn 5))
  (defj J26 () "MOVE(0)-(6) into W0-6" (J2n=move-0-to-n-into-w0-wn 6))
  (defj J27 () "MOVE(0)-(7) into W0-7" (J2n=move-0-to-n-into-w0-wn 7))
  (defj J28 () "MOVE(0)-(8) into W0-8" (J2n=move-0-to-n-into-w0-wn 8))
  (defj J29 () "MOVE(0)-(9) into W0-9" (J2n=move-0-to-n-into-w0-wn 9))

  (defj J30 () "RESTORE W0-W0" (J3n=restore-wn 0))
  (defj J31 () "RESTORE W0-W1" (J3n=restore-wn 1))
  (defj J32 () "RESTORE W0-W2" (J3n=restore-wn 2))
  (defj J33 () "RESTORE W0-W3" (J3n=restore-wn 3))
  (defj J34 () "RESTORE W0-W4" (J3n=restore-wn 4))
  (defj J35 () "RESTORE W0-W5" (J3n=restore-wn 5))
  (defj J36 () "RESTORE W0-W6" (J3n=restore-wn 6))
  (defj J37 () "RESTORE W0-W7" (J3n=restore-wn 7))
  (defj J38 () "RESTORE W0-W8" (J3n=restore-wn 8))
  (defj J39 () "RESTORE W0-W9" (J3n=restore-wn 9))

  (defj J40 () "PRESERVE W0-W0" (J4n=preserve-wn 0))
  (defj J41 () "PRESERVE W0-W1" (J4n=preserve-wn 1))
  (defj J42 () "PRESERVE W0-W2" (J4n=preserve-wn 2))
  (defj J43 () "PRESERVE W0-W3" (J4n=preserve-wn 3))
  (defj J44 () "PRESERVE W0-W4" (J4n=preserve-wn 4))
  (defj J45 () "PRESERVE W0-W5" (J4n=preserve-wn 5))
  (defj J46 () "PRESERVE W0-W6" (J4n=preserve-wn 6))
  (defj J47 () "PRESERVE W0-W7" (J4n=preserve-wn 7))
  (defj J48 () "PRESERVE W0-W8" (J4n=preserve-wn 8))
  (defj J49 () "PRESERVE W0-W9" (J4n=preserve-wn 9))

  (defj J50 () "PRESERVE W0-W0 THEN MOVE(0)-(0) into W0-W0" (J5n=preserve-wn-then-move-0-n-into-w0-wn 0))
  (defj J51 () "PRESERVE W0-W1 THEN MOVE(0)-(1) into W0-W1" (J5n=preserve-wn-then-move-0-n-into-w0-wn 1))
  (defj J52 () "PRESERVE W0-W2 THEN MOVE(0)-(2) into W0-W2" (J5n=preserve-wn-then-move-0-n-into-w0-wn 2))
  (defj J53 () "PRESERVE W0-W3 THEN MOVE(0)-(3) into W0-W3" (J5n=preserve-wn-then-move-0-n-into-w0-wn 3))

  (defj J60 (arg0) "LOCATE NEXT SYMBOL AFTER CELL (0)"
	;; LOCATE NEXT SYMBOL AFTER CELL (0). (0) is the name of a
	;; cell. If a next cell exists (LINK of (0) not a termination
	;; symbol), then the output (0) is the name of the next cell, and
	;; H5 is set +.  (!!! This whole "name" thing is an f'ing lie!
	;; It's the actual cell !!!)  If LINK is a termination symbol,
	;; then the output (0) is the input (0), which is the name of the
	;; last cell on the list, and H5 is set -. If the next cell is a
	;; private termination cell, J60 will work as specified above, but
	;; in addition, the private termination cell will be returned to
	;; available space and the LINK of the input cell (0) will be
	;; changed to hold 0. No test is made to see that (0) is not a
	;; data term, and J60 will attempt to interpret a data term as a
	;; standard IPL cell.
	(setf (h5) "+")
	;; De-ref symbol to list if necessary
	(setf arg0 (<== arg0)) 
	(let* ((this-cell arg0)
	       (link (cell-link this-cell)))
	  (!! :jfns "In J60, this-cell = ~s, link = ~s~%" this-cell link)
	  (if (zero? link)
	      (setf (h5) "-")
	      (setf (H0) (cell link)) ;; (h5) is already + from above
	      )))

  (defj J66 (arg0 arg1) "INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT"
	;; J66 INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT. A
	;; search of list (1) is made. against (0) (starting with the
	;; cell after cell (1) . If (0) is found, J66 does nothing
	;; further. If (0) is not found, it is inserted at the end of
	;; the list, as in J65. (??? What happens if the list
	;; branches??? At the moment this can't do anything sensible
	;; with a branching list!)
	(!! :jfns "J66 trying to insert ~s in ~s~%" arg0 arg1)
	(loop with list-cell = (<== arg1)
	      with symb = (if (stringp arg0)
			      arg0
			      (if (cell? arg0)
				  (cell-symb arg0)
				  (break "Error in J66: ~a should be a symbol or cell!" arg0)))
	      do
	      (cond ((string-equal (cell-symb list-cell) symb)
		     (!! :jfns "J66 found ~s in the list already. No action!~%" symb)
		     (return nil))
		    ((zero? (cell-link list-cell))
		     (!! :jfns "J66 hit end, adding ~s to the list!~%" symb)
		     (let* ((new-name (new-local-symbol (cell-name list-cell)))
			    (new-cell (make-cell! :name new-name :symb symb :link "0")))
		       (setf (cell-link list-cell) new-name)
		       (setf (cell new-name) new-cell)
		       (return t))))
	      ;; Move to next cell if nothnig above returned out
	      (setf list-cell (cell (cell-link list-cell)))))

  (defj J73 (arg0) "Copy list"
	;; COPYLIST (O). The output (0) names a new list, with the identical
	;; symbols in the cells as are in the corresponding cells of list (0),
	;; including the head. If (0) is the name of a list cell, rather that
	;; [sic: than] a head, the output (0) will be a copy of the remainder of
	;; the list from (0) on. (Nothing else is copied, not even the
	;; description list of (0), if it exists.)  The name is local if the
	;; input (0) is local; otherwise, it is internal.
	(setf (H0) (copy-ipl-list-and-return-head (<== arg0))))

  (defj J74 (arg0) "Copy List Structure"
	;; COPY LIST STRUCTURE (0). A new list structure is produced, the cells of
	;; which are in one-to-one correspondence with the cells of list structure
	;; (0). All the regional and internal symbols in the cells will be identical
	;; to the symbols in the corresponding cells of (0), as will the contents of
	;; data terms. There will be new local symbols, since these are the names of
	;; the sublists of the new structure. Description lists will be copied, if
	;; their names are local. If (0) is in auxiliary storage (Q of (0) = 6 or 7),
	;; the copy will be produced in main storage. In all cases, list structure (0)
	;; remains unaffected. The output (0) names the new list structure. It is
	;; local if the input (0) is local; It is internal otherwise.
	(!! :jfns "J74 is copying list: ~s~%" (H0))
	(setf (H0) (copy-list-structure arg0))
	)

  (defj J76 (arg0 arg1) "INSERT LIST (O) AFTER CELL (1) AND LOCATE LAST SYMBOL"
	;; INSERT LIST (O) AFTER CELL (1) AND LOCATE LAST SYMBOL. List (0) is
	;; assume to desescribable. Its head is erased (if local, the symbol in
	;; the head is erased as a list structure). The string of list cells is
	;; inserted after cell (1): LINK of cell (1) is the name of the first
	;; list cell, and LINK of the last cell of the string is the name of the
	;; cell originally occurring after cell (1). The output (0) is the name
	;; of the last cell in the inserted string and H5 is set +. If list (0)
	;; has no list cells, then the output (0) is the input (1) and H5 is set
	;; -. [Again, I think that this is intended only to work on linear lists
	;; since there's no "last symbol" in a non-linear list.]
	(let* ((l0 (<== arg0))
	       (c1 (<== arg1))
	       (c1link (cell-link c1))
	       (last-cell-in-l0 (last-cell-of-linear-list l0)))
	  (cond ((zero? (cell-link l0))
		 (setf (h0) c1)
		 (setf (h5) "-"))
		(t (setf (cell-link c1) (cell-link l0))
		   (setf (cell-link last-cell-in-l0) c1link)
		   (setf (h0) last-cell-in-l0)))))

  ;; J8n: FIND THE nth SYMBOL ON LIST (0) 0 <= n <= 9. (Ten routines: J80-J89)
  ;; Set H5 + if the nth symbol exists, - if not. Assume list (0) describable,
  ;; so that J81 finds symbol in first list cell, etc. J80 finds symbol in head;
  ;; and sets H5- if (0) is a termination symbol. 

  (defj J80 (arg0) "FIND THE HEAD SYMBOL OF (0)"
	(setf (H5) "+")
	(let* ((cell (<== arg0)))
	  (setf (H0) (cell-symb cell))
	  (if (zero? (cell-link cell)) (setf (H5) "-"))))
	
  (defj J81 () "Unimplemented!" (break "J81 is unimplemented!"))
  (defj J82 () "Unimplemented!" (break "J82 is unimplemented!"))

  ;; J9n CREATE A LIST OF THE n SYMBOLS (n-1), (n-2), ..., (1), (0), 0 <= n <=
  ;; 9. The order is (n-1) first, (n-2) second, ..., (0) last. The output (0) is
  ;; the name (internal) of the new list; it is describable. J90 creates an
  ;; empty list (also used to create empty storage cells, and empty data terms).

  (defj J90 () "Create a blank cell on H0"
	;; J90: Get a cell from the available space list, H2, and leave its name in HO.
	;; J90 creates an empty list (also used to create empty storage cells, and empty data terms).
	;; The output (0) is the name a the new list.
	(let* ((name (new-local-symbol "L"))
	       (cell (make-cell! :name name :symb "0" :link "0")))
	  (setf (cell name) cell)
	  (!! :jfns "J90 creating blank list cell: ~s~%" cell)
	  (store cell)
	  (vv "H0" cell)))

  (defj J91 () "Unimplemented!" (break "J91 is unimplemented!"))
  (defj J92 () "Unimplemented!" (break "J92 is unimplemented!"))
  (defj J93 () "Unimplemented!" (break "J93 is unimplemented!"))

  (defj J100 (arg0 arg1) "GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0)"
	;; J100 GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0). The subprocess
	;; named (0) is performed successively with each of the symbols of list named
	;; (1) as input. The order is the order on the list, starting with the first
	;; list cell. H5 is always set + at the start of the subprocess. J100 will
	;; move in list (1) if it is on auxiliary. [This assumes a linear list.]
	(loop with cell-name = (cell-link (<== arg1))
	      with cell
	      until (zero? cell-name)
	      do 
	      (setf cell (cell cell-name))
	      (vv "H0" (cell-symb (cell cell)))
	      (setf (H5) "+")
	      (ipl-eval arg0)
	      (^^ "H0")
	      (setf cell-name (cell-link cell))
	      ))

  (defj J111 (arg0 arg1 arg2) "(1) - (2) -> (O)."
	;; The number (0) is set equal to the a gebraic difference between numbers
	;; (1) and (2). The output (0) is the input (0).
	(let* ((n1 (num?get arg1))
	       (n2 (num?get arg2))
	       (r (- n1 n2)))
	  (!! :jfns "J111: ~a - ~a = ~a~%" n1 n2 r)
	  (let ((H0 (<== (H0))))
	    (setf (cell-link H0) r))))

  (defj J117 (arg0) "TEST IF (O) = 0."
	(let* ((n (num?get arg0)))
	  (!! :jfns "J117: Testing if ~s (~s: ~s) = 0?~%" arg0 (<== arg0) n)
	  (if (zerop n) (setf (H5) "+") (setf (H5) "-"))))

  (defj J120 (arg0) "COPY (0)"
	;; COPY (0). The output (0) names a new cell containing the identical
	;; contents to (0). The name is local if the input (0) is local; other-
	;; wise, it is internal.
	(let* ((old-cell (<== (H0)))
	      (new-cell (copy-cell old-cell))
	      (new-name (new-local-symbol)))
	  (setf (cell-name new-cell) new-name)
	  (!! :jfns "Copied ~s -> ~s into H0.~%" old-cell new-cell)
	  (store new-cell)
	  (setf (H0) new-cell)))

  (defj J124 () "CLEAR (0)"
	;; The number (0) is set to be 0. If the ce 1is not a data term, it is
	;; made an in- teger data term= 0. If a number, its type, integer, or
	;; floating point, is unaffected. It is left as the output (0).
	(let ((H0 (<== (H0))))
	  (!! :jfns "J124: Clear (H0): ~s~%" H0)
	  (setf (cell-link H0) 0)))

  (defj J125 () "TALLY1 IN (0)"
    ;; An integer 1 is added to the number (0). The type of the result is the
    ;; same as the type of (0). It is left as the output (0).
    (let ((H0 (<== (H0))))
      (!! :jfns "J125: Tally (H0): ~s~%" H0)
      (setf (cell-link H0) (1+ (cell-link H0)))))

  (defj J130 (H0) "TEST IF (O) IS REGIONAL SYMBOL"
	;; Tests if Q = 0 in H0.
	(if (zerop (getpq :q (cell-pq (<== H0))))
	    (setf (H5) "+") (setf (H5) "-")))

  (defj J148 () "MARK ROUTINE (0) TO PROPAGATE TRACE."
	;; Identical to Jl47, except uses Q = 4.
	(!! :jfns "J148 (MARK ROUTINE (0) TO PROPAGATE TRACE.) is a noop."))

  ;; Input and output are completely kludged, and unlike in original IPL. Partly
  ;; this is required because we don't have the same sort of physical
  ;; environment. There are tapes, and so on. But also, partly it's for
  ;; kludge-convenience. For example, there is exactly one 80 column
  ;; input/output buffer and it's used for all input and output.

  (defj J151 (arg0) "Print list (0)"
	(line-print-linear-list arg0))

  (defj J152 () "PRINT SYMBOL (0)"
	(line-print-cell (H0)))

  (defj J154 () "Clear print line"
	;; Clear Print Line CLEAR PRINT LINE. Print line 1W24 is cleared and the
	;; current entry column, 1W25, is set equal to the left margin, 1W21 [always 1 at the moment].
	(setf *W24-Line-Buffer* (blank80))
	(setf (cell-link (cell "W25")) 1))


  (defj J180 () "READ LINE J180 READLINE"
	;; The next record on unit 1W18 is read to line 1W24. (The record is
	;; assumed to be BCD, 80 cols.) Column 1 of the record is read into
	;; column 1 of the read line, and so forth. H5 is set+. If no record can
	;; be read (end-of-file condition), the line is not changed and HS is
	;; set - . [Note that 1W24 is ignored here and the input is put into our
	;; global single-line store: *W24-Line-Buffer*. Also, we set W25, the read
	;; position to numerical 1.]
	(let ((line (read-line *input-stream* nil nil)))
	  (!! :io "J180 Read:~%~s~%%" line)
	  (setf (h5) "+")
	  (if line (scan-input-into-*W24-Line-Buffer* line)
	      (setf (h5) "-"))
	  (setf (cell-link (cell "W25")) 0)
	  ))
	
  (defj J181 () "INPUT LINE SYMBOL."
	;; INPUT LINE SYMBOL. The IPL symbol in the field starting in column
	;; 1W25, of size 1W30, in line 1W24, is input to HO and H5 is set +. The
	;; symbol is regional if the first (leftmost) column holds a regional
	;; character; otherwise, it is absolute internal. All non-numerical
	;; characters except in the first column are ignored. If the field is
	;; entirely blank, or ignored, there is no input to HO, and H5 is set
	;; -. In either case, 1W25 is incremented by the amount 1W30. (J181
	;; turns unused regional symbols into empty but used symbols.)
	(let* ((w25 (cell "W25"))
	       (w25p (cell-link w25))
	       (w30 (cell "W30"))
	       (w30n (cell-link w30))
	       (start (- (1+ w25p) 2))
	       (end (+ 1 start w30n))
	       (string (subseq *W24-Line-Buffer* start end)))
	  (!! :jfns "J181 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a]~%" string start end *W24-Line-Buffer* w25p w30n)
	  (incf (cell-link w25) w30n) 
	  (if (j181-helper-is-regional-symbol? string)
	      (progn
		(!! :jfns "J181 decided that ~s IS a regional symbol.~%" string)
		(setf (H0) string) (setf (H5) "+"))
	      (progn
		(!! :jfns "J181 decided that ~s is NOT a regional symbol.~%" string)
		(setf (H5) "-")))))

  ;; J183 SET (0) TO NEXT BLANK. (0) is taken as a decimal integer data
  ;; term. Line 1W24 is scanned, left to right, starting with column 1W25+1, for
  ;; a blank. One is added to (0) for each column scanned, including that in
  ;; which the scanned-for character ('blank' in J183) is found. (0) is left as
  ;; output (0). H5 is set + if the character is found in the line, and - if it
  ;; is not. (Thus, if input (0) = 1W25, after scanning, output (0) will specify
  ;; the column holding the scanned-for character. If input (0) = decimal
  ;; integer 0, after scanning, output (0) will be the size of a field beginning
  ;; in column 1W25 and delimited on the right by the next occurrence of the
  ;; scanned-for character.)

  (defj J183 (arg0) "SET (0) TO NEXT BLANK"
	(J183/4-Scanner arg0 :blank))
 
  ;; J184 SET (0) TO NEXT NON-BLANK. Same as J183, except scans for any
  ;; non-blank character.

  (defj J184 (arg0) "SET (0) TO NEXT NON-BLANK"
	(J183/4-Scanner arg0 :non-blank))

  (defj J71 () "Unimplemented!" (break "J71 is unimplemented!"))
  (defj J136 () "Unimplemented!" (break "J136 is unimplemented!"))
  (defj J10 () "Unimplemented!" (break "J10 is unimplemented!"))
  (defj J155 () "Unimplemented!" (break "J155 is unimplemented!"))
  (defj J72 () "Unimplemented!" (break "J72 is unimplemented!"))
  (defj J5 () "Unimplemented!" (break "J5 is unimplemented!"))
  (defj J2 () "Unimplemented!" (break "J2 is unimplemented!"))
  (defj J11 () "Unimplemented!" (break "J11 is unimplemented!"))
  (defj J161 () "Unimplemented!" (break "J161 is unimplemented!"))
  (defj J160 () "Unimplemented!" (break "J160 is unimplemented!"))
  (defj J157 () "Unimplemented!" (break "J157 is unimplemented!"))
  (defj J64 () "Unimplemented!" (break "J64 is unimplemented!"))
  (defj J116 () "Unimplemented!" (break "J116 is unimplemented!"))
  (defj J7 () "Unimplemented!" (break "J7 is unimplemented!"))
  (defj J14 () "Unimplemented!" (break "J14 is unimplemented!"))
  (defj J133 () "Unimplemented!" (break "J133 is unimplemented!"))
  (defj J18 () "Unimplemented!" (break "J18 is unimplemented!"))
  (defj J68 () "Unimplemented!" (break "J68 is unimplemented!"))
  (defj J17 () "Unimplemented!" (break "J17 is unimplemented!"))
  (defj J19 () "Unimplemented!" (break "J19 is unimplemented!"))
  (defj J65 () "Unimplemented!" (break "J65 is unimplemented!"))
  (defj J75 () "Unimplemented!" (break "J75 is unimplemented!"))
  (defj J78 () "Unimplemented!" (break "J78 is unimplemented!"))
  (defj J138 () "Unimplemented!" (break "J138 is unimplemented!"))
  (defj J137 () "Unimplemented!" (break "J137 is unimplemented!"))
  (defj J115 () "Unimplemented!" (break "J115 is unimplemented!"))
  (defj J182 () "Unimplemented!" (break "J182 is unimplemented!"))
  (defj J114 () "Unimplemented!" (break "J114 is unimplemented!"))
  (defj J126 () "Unimplemented!" (break "J126 is unimplemented!"))
  (defj J30 () "Unimplemented!" (break "J30 is unimplemented!"))
  (defj J15 () "Unimplemented!" (break "J15 is unimplemented!"))
  (defj J166 () "Unimplemented!" (break "J166 is unimplemented!"))
  (defj J0 () "Unimplemented!" (break "J0 is unimplemented!"))
  (defj J1 () "Unimplemented!" (break "J1 is unimplemented!"))
  (defj J79 () "Unimplemented!" (break "J79 is unimplemented!"))
  (defj J156 () "Unimplemented!" (break "J156 is unimplemented!"))
  (defj J186 () "Unimplemented!" (break "J186 is unimplemented!"))
  (defj J62 () "Unimplemented!" (break "J62 is unimplemented!"))
  (defj J110 () "Unimplemented!" (break "J110 is unimplemented!"))
  (defj J147 () "Unimplemented!" (break "J147 is unimplemented!"))

  )




;;; ===================================================================
;;; JFn Utilities

(defparameter *LT-Regional-Chars* "ABCDEFGIKLMNOPQRSTUVXYZ-*=,/+.()'")

(defun j181-helper-is-regional-symbol? (string)
  (and (find (aref string 0) *LT-Regional-Chars*)
       (loop for p from 1 by 1
	     with lim = (1- (length string))
	     until (= p lim)
	     if (not (find (aref string p) "0123456789."))
	     do (return nil)
	     finally (return t))))

(defun num?get (sym)
  (let* ((cell (<== sym))
	 (n (cell-link cell)))
    (if (numberp n) n
	(break "In ~a, asked to test a non-number: ~s from ~s (~s)." n cell sym))))
    
;;; !!! WWW OBIWAN UNIVERSE WITH LISP ZERO ORIGIN INDEXING WWW !!!

(defun J183/4-Scanner (arg0 mode)
  (let* ((H0 (<== arg0))
	 (w25p (cell-link (cell "W25")))
	 (h0p (cell-link H0)))
    (!! :jfns "Starting in J183/4-Scanner: H0 = ~s, w25p = ~a, h0p = ~%" H0 w25p h0p)
    (if (not (numberp h0p)) (break "In J183/4 expected H0(p) (~a) to be a number.~%" (H0)))
    (if (not (numberp w25p)) (break "In J183/4 expected W25(p) (~a) to be a number.~%" (cell "W25")))
    (setf (H5) "-")
    (incf w25p)		    ;; Start at W25+1 (per manual)
    (loop until (= w25p 80) 
	  ;; WWW OBIWON !!! The only place I should have to correct this is here (I hope!) 
	  as char = (aref *W24-Line-Buffer* (1- w25p))
	  do 
	  (!! :jfns "Deep in J183/4-Scanner: w25p = ~a, char = ~s, h0p = ~%" w25p char h0p)
	  (when (case mode
		  (:blank (char-equal char #\space))
		  (:non-blank (not (char-equal char #\space)))
		  (t (error "!!! J183/4-Scanner given unknown mode: ~s" mode)))
	    (setf (cell-link H0) h0p)
	    ;;(setf (cell-link (cell "W25")) w25p) ;; I don't think that this gets reset !!! ???
	    (setf (H5) "+")
	    (return t))
	  (incf H0p) (incf w25p)
	  )))

(defun scan-input-into-*W24-Line-Buffer* (line)
  (loop for c across line
	as p from 0 by 1
	do (setf (aref *W24-Line-Buffer* p) c))
  (!! :jfns "Read into *W24-Line-Buffer*: ~s~%" *W24-Line-Buffer*))

(defun J2n=move-0-to-n-into-w0-wn (n)
  (setf (cell "W0") (H0))
  (loop for nn from 1 to n ;; Won't do anything if n=0
	as val in (H0+)
	do (setf (cell (format nil "W~a" nn)) val)))

(defun J3n=restore-wn (n)
  (loop for nn from 0 to n do (^^ (format nil "W~a" nn))))

(defun J4n=preserve-wn (n)
  (loop for nn from 0 to n do (vv (format nil "W~a" nn))))

(defun J5n=preserve-wn-then-move-0-n-into-w0-wn (n)
  (J4n=preserve-wn n)
  (J2n=move-0-to-n-into-w0-wn n))

(defvar *copy-list-collector* nil)

(defun copy-ipl-list-and-return-head (head)
  (setf *copy-list-collector* nil)
  (copy-ipl-list (<== head) (new-local-symbol))
  (store-cells *copy-list-collector*)
  (car (last *copy-list-collector*)))

(defun copy-ipl-list (cell-or-symb/link &optional new-cell-name)
  (cond
    ;; If you're handed a cell, create a new one
    ((cell? cell-or-symb/link)
     (let ((new-name (or new-cell-name (new-local-symbol))))
       (push (make-cell! :name new-name
			:symb (copy-ipl-list (cell-symb cell-or-symb/link))
			:link (copy-ipl-list (cell-link cell-or-symb/link)))
	     *copy-list-collector*)
       new-name))
    ;; If you get a zero, just return it to get pluged back in.
    ((zero? cell-or-symb/link) "0")
    ;; If it's a local symbol, create a new cell with a new symbol and copy the cell,
    ;; recursing for the symb and links
    ((local-symbol? cell-or-symb/link)
     (let ((new-name (new-local-symbol)))
       (push (make-cell! :name new-name
				:symb (copy-ipl-list (cell-symb cell-or-symb/link))
				:link (copy-ipl-list (cell-link cell-or-symb/link)))
	     *copy-list-collector*)
       new-name))
    ;; If we're handed a global symbol, just return it.
    ((global-symbol? cell-or-symb/link)
     cell-or-symb/link)
    (t (break "In copy-ipl-list got ~s which wasn't expected." cell-or-symb/link))))

(defun copy-list-structure (l)
  (break "COPY-LIST-STRUCTURE is probably wrong!")
  (if (zero? l) l ;; End of sublist, just return the EOsL "0"
      (let ((new-name (new-local-symbol)))
	(setf (gethash new-name *symtab*) (mapcar #'copy-list-cell l))
	new-name)))

(defun copy-list-cell (cell)
  (if (zero? cell) cell ;; End of sublist, just return the EOsL "0"
      (let* ((new-cell (copy-cell cell)))
	(setf (cell-name new-cell) (new-local-symbol))
	;; WWW ??? This has the problem that it's going to copy whole functions
	;; into copied lists, which is probably not what is intended. Maybe
	;; things that are defined in the load process shouldn't be copied? 
	(setf (cell-symb new-cell) (copy-list-structure (cell-symb cell)))
	(setf (cell-link new-cell) (copy-list-structure (cell-link cell)))
	)))
	
(defun last-cell-of-linear-list (l)
  (cond ((zero? (cell-link l)) l)
	(t (last-cell-of-linear-list (cell (cell-link l))))))

;;; This only prints lists that are linked via their LINK symbols.

(defun line-print-linear-list (cell)
  (setf cell (<== cell))
  (format t "~%+---------------------------------------------------------------------+~%")
  (loop do (format t "| ~s~70T|~%" cell)
	(let ((link (cell-link cell)))
	  (if (zero? link) (return :end-of-list))
	  (setf cell (cell link))))
  (format t "+---------------------------------------------------------------------+~%")
  )

(defun line-print-cell (cell)
  (setf cell (<== cell))
  (format t "~%+---------------------------------------------------------------------+~%")
  (format t "| ~s~70T|~%" cell)
  (format t "+---------------------------------------------------------------------+~%")
  )

;;; =========================================================================
;;; Emulator core

;;; Directly implements "3.15 THE INTERPRETATION CYCLE", pg. 164 of
;;; the IPL-V manual. It can actually be called recursively...but the
;;; caller has to keep track of H1. IPL code implements recursion "the
;;; hard way", so there's generally no need to call this fn
;;; recursively.

(defvar *adv-limit* nil)

(defun run (start-symb &key (adv-limit 1000))
  (initialize-machine)
  (!! :run "********** Starting run at ~a with adv-limit = ~a **********~%" start-symb adv-limit)
  (setf *adv-limit* adv-limit)
  (setf *running?* t)
  (ipl-eval (cell start-symb))
  (setf *running?* nil)
  (if (member :end-dump *!!list*) (report-system-cells))
  )

(defun initialize-machine ()
  (create-system-cells) ;; See above in storage section
  (setf (h5+) (list "+")) ;; Init H5 +
  (setf (cell-link (cell "H3")) 0) ;; Init H3 Cycle-Counter
  (setf *W24-Line-Buffer* (Blank80)) ;; Init Read Line buffer
  (setf (cell-symb (cell "W25")) 1) ;; Init read/print position
  )

(defun ipl-eval (start-cell)
  (!! :run "vvvvvvvvvvvvvvv Entering IPL-EVAL at ~s" start-cell)
  (prog (cell pq q p symb link)
     (setf (h1) (make-cell! :name (gensym) :symb "exit"))
     (vv "H1" start-cell) ;; Where we're headed this time in.
     ;; Indicates (local) top of stack for hard exit (perhaps to recursive call)
   INTERPRET-Q 
     (!! :run-full "---> At INTERPRET-Q w/H1 = ~s! (*fname-hint* = ~s)~%" (h1) *fname-hint*)
     ;; H1 contains the name of the cell holding the instruction to be
     ;; interpreted. At this point it could be a symbol or a list. If it's a
     ;; symbol, we need to de-reference it to the list. In the case of an
     ;; internal (J) funtion this will be a lambda, in which case we just call
     ;; it and then advance
     (when (null (H1)) (break "!!! PROBABLY MISSING A JFN DEFINITION !!!"))
     (when (functionp (h1))
       (let* ((arglist (second (function-lambda-expression (H1))))
	      (args (if (null arglist) ()
			(cons (H0)
			      (loop for arg in (cdr arglist)
				    as val in (h0+)
				    collect val)))))
	 (!! :run ">>>>>>>>>> Calling ~a [~a]~%           ~s = ~s~%"
	     *fname-hint* (getf (gethash *fname-hint* *jfn-plists*) 'explanation) arglist args)
	 (apply (H1) args))
       (^^ "H1") ;; Remove the JFn call
       (go ADVANCE)
       )
     (setq cell (H1)) ;; This shouldn't be needed since we're operating all in cell now.
     (!! :run "~%>>>>>>>>>> Executing: ~s (~a)~%" cell *adv-limit*)
     (setf *trace-instruction* cell) ;; For tracing and error reporting
     (setf pq (cell-pq cell)
	   q (getpq :q pq)
	   p (getpq :p pq)
	   symb (cell-symb cell)
	   link (cell-link cell)
	   )
     (!! :run-full "~%-----> At INTERPRET-Q: CELL =~s~%      Q = ~s, symb=~s~%" cell q symb)
     (case q
       ;; 0 take the symbol itself
       (0 (setf (s) symb) (go INTERPRET-P))
       ;; 1 Take the name the symbol is pointing to
       (1 (setf (s) (cell symb)) (go INTERPRET-P))
       ;; 2 Take the symbol in the cell at the name that the symb is pointing to
       (2 (setf (s) (cell (cell-name% (cell symb)))) (go INTERPRET-P))
       (3 (!! :run "(Unimplemented monitor action in ~s; Executing w/o monitor!)~%" cell) (setf (s) symb) (go INTERPRET-P))
       (4 (!! :run "(Unimplemented monitor action in ~s; Executing w/o monitor!)~%" cell) (setf (s) symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go ASCEND)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!" cell))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!" cell))
       )
   INTERPRET-P 
     (!! :run-full "-----> At INTERPRET-P w/P = ~s, (s)=~s~%" p (s))
     (case p
       (0 (go TEST-FOR-PRIMITIVE))
       (1 (vv "H0" (S)))                    ;; Input S (after preserving HO) 
       (2 (setf (cell (S)) (H0)) (^^ "H0")) ;; Output to S (then restore HO)
       (3 (^^ (s)))                         ;; Restore (pop up) S 
       (4 (vv (S)))                         ;; Preserve (push down) S
       (5 
	;; Replace (0) by S -- Here if S is just a symbol we need to either get
	;; it, or make a cell to hold it because it's just a list symbol
	;; (string, actually) (But if H0 is already a cell we can just replace
	;; it.)
	(setf (H0) (<== (s)))
	)
       (6 (setf (s) (cell-symb (H0))))      ;; Copy (0) in S -- opposite of 5, and we unpack the cell to a symbol.
       (7 (go BRANCH)) ;; Branch to S if H5-
       )
     (go ADVANCE)
   TEST-FOR-PRIMITIVE 
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (!! :run-full "-----> At TEST-FOR-PRIMITIVE w/S = ~s, Q = ~s, symb=~s~%" (s) q symb)
     (case q 
       (5 (setf link (s)) (go ADVANCE))
       (t (go DESCEND)))
   ADVANCE (!! :run-full "-----> At ADVANCE")
     (if (and *adv-limit* (zerop (decf *adv-limit*)))
	 (break " !!!!!!!!!!!!!! IPL-EVAL hit *adv-limit* !!!!!!!!!!!!!!"))
     (incf (cell-link (cell "H3")))
     (when (string-equal (cell-symb (h1)) "exit")
       (!! :run "Exiting from IPL-EVAL ^^^^^^^^^^^^^^^")
       (^^ "H1") (return))
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (cell-link (H1)))
   ADVANCE-W/FORCED-LINK (!! :run-full "-----> At ADVANCE-W/FORCED-LINK (link=~s)" link)
     (clean-stacks)
     ;; If link is nil ("") in the middle of a function, go next cell, else ascend.
     (if (zero? link) (go ASCEND))
     ;; Note that if there is a link to a different function
     ;; (commonly J31, which resets W0 and W1), then when THAT
     ;; function terminates the whole prog sequence
     ;; ascends. This is a somewhat confusing yet common way to
     ;; end a function, that is, by branching off to a J
     ;; function which, when it completes, pops to whereever its
     ;; caller came from.
     (setf (h1) (cell link))
     (go INTERPRET-Q)
   ASCEND 
     (!! :run-full "-----> At ASCEND w/H1 = ~s~%" (h1))
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (^^ "H1")
     (go ADVANCE)
   DESCEND 
     (!! :run-full "-----> At DESCEND w/S = ~s~%" (s))
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (setf *fname-hint* (s))
     (vv "H1" (cell (s)))
     (go INTERPRET-Q)
   BRANCH 
     (!! :run-full "-----> At BRANCH w/H5 = ~s, S= ~s~%" (h5) (s))
     ;; Interpret Sign in H5: - H5-: Put S as LINK (control transfers to S); go
     ;; to ADVANCE. - H5+: Go to ADVANCE
     (when (string-equal (h5) "-") (setf link (s)) (go ADVANCE-W/FORCED-LINK))
     (go ADVANCE)
     ))

(defun call-ipl-prim (symb)
  (break "!!!!!!!! UNIMPLEMENTED: (call-ipl-prim ~s)" symb))

;;; Getting the P and Q is a little tricky because they can be blank. Blank is
;;; interpreted as zero, and if they're both blank ("") it's not a problem --
;;; both zero, but if only one is blank it can be ambiguous because these didn't
;;; come from cells. This isn't suppose to happen, so if it does, we raise a
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

;;; =========================================================================
;;; Utilities

(defun core-dump (table)
  (format t "~a contains ~a entries:~%" table (hash-table-count table))
  (loop for key being the hash-keys of table
	using (hash-value value)
	do (format t "~s => ~s~%" key value)))

;;; =========================================================================
;;; Test calls

(define-symbol-macro rsc (report-system-cells))
(define-symbol-macro rsc* (report-system-cells t))
(untrace)
(trace ipl-eval run)
(setf *stack-depth-limit* 100) ;; FFF ? Localize ?
(setf *!!list* '()) ;; :deep-memory :load :run :jfns :run-full :io :end-dump (t for all)
(load-ipl "F1.lisp")
(load-ipl "Ackermann.iplv" :adv-limit 100000)
(if (= 61 (cell-link (cell "N0")))
    (format t "~%*********************************~%* Ackerman (3,3) = 61 -- Check! *~%*********************************~%")
  (error "Oops! Ackermann (3,3) should have been 61, but was ~s" (cell "N0")))
(trace j181-helper-is-regional-symbol? J183/4-Scanner)
(setf *trace-cell-names* '("W25" "W26" "W30"))
(setf *!!list* '(:run-full :run :jfns)) ;; :deep-memory :load :run :jfns :run-full :io :end-dump (t for all)
(load-ipl "LTFixed.lisp")

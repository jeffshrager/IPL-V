;;; (load (compile-file "iplv.lisp"))

#|

Current issue:

At P050R020::{P50+39139/70/J8/P50+39140} called from calls J8 correctly (although
it doesn't tell us that it's doing it, but tracing J8 tells us tht it
does). But and then returns -- I guess correctly to X1-9-2

Here's the seq:

!![RUN]::>>>>>>>>>> Executing: {P050R010::P50+43534//P15/P50+43535 [INTERNAL (TREE) FORM IF IN/]} (9736)
!![RUN]::>>>>>>>>>> Executing: {P015R000::P15//Q15/P15+43382 [P15 TEST IF (V) IS IN /]} (9736)
!![RUN]::>>>>>>>>>> Executing: {Q015R000::Q15/10/Q15/J10 [Q15 ATTRIBUTE INTERNAL FORM./]} (9736)
!![RUN]::>>>>>>>>>> Calling Q15 [NIL] (ARG0 ARG1) = ("Q15" "*101")
!![JFNS]::In J10 trying to find the value of "Q15" in "*101"!
!![JFNS]::J10 failed to find "Q15".
!![RUN]::>>>>>>>>>> Executing: {P015R010::P15+43382/70/0/J8 [   INTERNAL (TREE) FORM./]} (9734)
!![RUN]::>>>>>>>>>> Executing: {P050R020::P50+43535/70/J8/P50+43536 [EXTERNAL (LIST) FORM. ENTIRE/]} (9733)
"[Invisible J8 call]"
!![RUN]::>>>>>>>>>> Executing: {X001R140::X1+44155/70/X1-9-2/X1+44156} (9732)
!![RUN]::>>>>>>>>>> Executing: {X001R160::X1-9-2//X1-9-100/X1-9-1 [TAKE ACTION, TRY FOR ANOTHER/]} (9732)
!![RUN]::>>>>>>>>>> Executing: {X001R300::X1-9-100/40/H0/X1+44168 [BAD INPUT ACTION./]} (9732)

(Note the J8 error popping stack motif!)


PQ Meaning for all PQ used in LT:
---------------------------------
00 (blank) Execute fn named by symb name per se (*)
01 Execute fn contained in cell named by symb (*>)
04 (blank) Execute fn named by symb name per se (same as 00 bcs no tracing) (>)
10 Push the symb (name) itself on H0 (*>)
11 Push content of the cell named by symb, onto H0 (*>)
12 Push 2nd deref on H0 (*>>)
14 Push the symb (name) itself on H0 (same as 10 bcs no tracining) (*)
20 Move H0 to the named symbol (per se) and pop (restore) H0. (*)
   (? This is a little weird bcs it seems like you should be moving
      the value to the command itself!)   
21 Move H0 to the cell named by symb, and pop (restore) H0. (*>)
30 Pop the named stack (per se) (*)
31 Pop the stack of the sym in the named cell (1st ref) (*>)
32 Pop the stack of the 2nd derefed cell (*>>)
40 Push down (preserve) the named symb (per se)
50 Replace H0 by the named symb (per se) (*)
51 Replace H0 by the cell named in the H0 symb (*>)
52 Replace H0 2nd deref (*>>)
60 Set the symb name per se to H0 (or cell named by H0 if string) (*)
64 Set the symb name per se to H0 (or cell named by H0 if string) (Same as 60 (no tracing)) (*)
70 Branch to symb name (per se) if H5- (*)

It seems that all JFns will remove their inputs, e.g., p.10: "...it is
understood from the definition of TEST that J2 will remove both (0)
and (1) from HO."

To Do (or at least think about):

FFF Normalize the poph0 (to the extent possible) and fold into DefJ?

WWW Noting handles multiply-nested dlists!

WWW A lot of code assumes that a list isn't branching -- e.g., DLIST
processing.

??? FFF Should W24 (read/print line) be in an actual cell? Right now it's in a
special global that can only process on line of I or O at a time.

FFF Need to find out where the memory leaks are that are leaving junk on the
stacks (primarily H0) -- I think it's the Jfns that aren't cleaning up after
themselves, and/or not absorbing their inputs.

FFF There's a hack for true blanks in both symb and link in LT:/016D070 to avoid
the load-time trap. Eventually, test for data mode 21 to allow both blanks.

WWW If J65 tries to insert numeric data there's gonna be a problem bcs PQ will be wrong.

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
(defun cell? (cell?) (eq 'cell (type-of cell?)))
(defmacro stack (symb) `(gethash ,symb *systacks*)) ;; Only system cells have stacks


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
  ;;(trace-cell-or-name? ssname)
  (setf (cell ssname) (pop (stack ssname))))
(defun vv (ssname &optional new-value)
  ;;(trace-cell-or-name? ssname)
  (push (cell ssname) (stack ssname))
  (when new-value (setf (cell ssname) new-value)))

;;; This is a protected version of cell-name that de-refs if necessary.

(defun cell-name% (cell-or-name)
  (cell-name (<== cell-or-name)))

(defun <== (cell-or-name &key create-if-does-not-exist?) ;; de-ref-or-die
  (let ((cell (if (cell? cell-or-name) cell-or-name
		  (if (stringp cell-or-name) (cell cell-or-name)))))
    (!! :deep-memory "<== Retreive == ~s = ~s [mem]~%" cell-or-name cell)
    (if (cell? cell) cell
	(if create-if-does-not-exist?
	    (make-cell! :name cell-or-name)
	    (error "Trying to deref ~s, which isn't a cell, while executing ~s!" cell-or-name *trace-instruction*)))))

(defun new-local-symbol (&optional (prefix "9")) (format nil "~a~a" prefix (gensym "+")))

(defmacro make-cell! (&rest args)
  `(store (make-cell ,@args)))

(defun store (cell &optional (name (cell-name cell)))
  (!! :deep-memory "== Store ==> ~s [mem]~%" cell)
  (setf (gethash name *symtab*) cell)
  cell)
  
;;; This can trace strings, or any element (name/symb/link) of a cell
;;; incl. stackables.

(defvar *running?* nil)

;;; This is temporarily deprecated bcs it fails tracing H0 (and some
;;; others) that can contain strings.

(defun trace-cell-or-name? (cell-or-name)
  (break "trace-cell-or-name? is temporarily deprecated")
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

;;; This is used in the internals of the interpreter so it has to be efficient.

(defun trace-cells ()
  (when *trace-cell-names* (format t "========= CELL TRACE:~%"))
  (loop for name in *trace-cell-names* do (format t "   ~a=~s |" name (cell name)))
  (when *trace-cell-names* (format t "~%"))
  (loop for name in *trace-cell-names* do (format t "      ~a+=~s~%" name (first-n 5 (gethash name *systacks*)))))

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
(defvar *breaks* nil) ;; If this is set to * it break on every call

;;; FFF Maybe make this a optional progn so that we don't have to put progns all
;;; over the place in order to trace.

(defun !! (key fmt &rest args)
  ;; WWW if the arg is actually nil, apply gets confused so we pre-fix this case.
  (unless args (setf args '(())))
  (when (or (equal *!!list* t)
	    (equal key t)
	    (member key *!!list*))
    (format t "!![~a]::" key)
    (apply #'format t fmt args)
    (when (and (member key '(:run :run-full)) (member :run-full *!!list*))
      (report-system-cells)))
  )

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
(define-symbol-macro rsc (report-system-cells))
(define-symbol-macro rsc* (report-system-cells t))
(define-symbol-macro rcs (report-system-cells))
(define-symbol-macro rcs* (report-system-cells t))
(define-symbol-macro lb *W24-Line-Buffer*)
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

;;; WWW You's think we could pop the input args off H0 automatically,
;;; but some IPL code leave the input args in place on purpose. See
;;; PopH0 utility. Some jfns destroy the (0) by replacing it with the
;;; output. In this case you don't want to pop bcs you'll lose the
;;; result.

(defmacro defj (name args explanation &rest forms)
  `(let ((uname ,(string-upcase (format nil "~a" name))))
     (setf (gethash uname *jfn-plists*) '(explanation ,explanation))
     (setf (gethash uname *symtab*)
	   (lambda ,args
	     ,@forms))))

(defun setup-j-fns ()

  (defj J0 () "No operation")
  (defj J2 (arg0 arg1) "TEST (0) = (1)?"
	;; Pop?
	(setf (h5) (if (equal arg0 arg1) "+" "-")))
  (defj J3 () "SET H5 -" (setf (H5) "-"))
  (defj J4 () "SET H5 +" (setf (H5) "+"))
  (defj J5 () "REVERSE H5"
	(if (string-equal "+" (H5))
	    (setf (H5) "-")
	    (setf (H5) "+")))

  (defj J6 () "REVERSE (0) and (1)" ;; WWW H1 is not (1)
	(let ((z (H0)))
	  (setf (H0) (first (H0+)))
	  (setf (first (H0+)) z)))

  (defj J8 () "RESTORE H0" (^^ "H0"))

  ;; I don't think that this is necessary as we don't need to do our own GC.
  (defj J9 (a0) "ERASE CELL (0)"
	(!! :jfns "J9 is a noop as we don't need to do our own GC.~%")
	(poph0 1))

  (defj J10 (arg0 arg1) "FIND THE VALUE OF ATTRIBUTE (0) OF (1)"
	;; If the symbol (0) is on the description list of list (1) as an
	;; attribute, then its value--i.e., the symbol following it--is output
	;; as (0) and H5 set + ; if not found, or if the description list
	;; doesn't exist, there is no output and H5 set - . (J10 is accomplished
	;; by a search and test of all attributes on the description list.)
	(PopH0 2)
	(!! :jfns "In J10 trying to find the value of ~s in ~s!~%" arg0 arg1)
	(let* ((list-head (<== arg1))
	       (dlist-name (cell-symb list-head))
	       (att-name (if (stringp arg0) arg0 (cell-symb arg0))))
	  (!! :jfns "In J10 list-head = ~s, dlist-name = ~s, att-name = ~s~%" list-head dlist-name att-name)
	  (if (zero? dlist-name)
	      (progn
		(!! :jfns "In J10 -- no dl, so we're done with H5-~%")
		(setf (H5) "-"))
	      (loop with dl-attribute-cell = (cell (cell-link (<== dlist-name)))
		    do ;; Note we're skipping the dl of the dl if any
		    (!! :jfns "In J10 dl-attribute-cell = ~s~%" dl-attribute-cell)
		    (if (string-equal att-name (cell-symb dl-attribute-cell))
			(let* ((val (cell (cell-link dl-attribute-cell))))
			  (!! :jfns "J10 found ~s at ~s, returning ~s~%" att-name dl-attribute-cell val) 
			  (setf (H5) "+") (setf (H0) val) (return t))
			(let* ((next-att-link (cell-link dl-attribute-cell)))
			  (if (zero? next-att-link)
			      (progn
				(!! :jfns "J10 failed to find ~s.~%" att-name)
				(setf (H5) "-") (return nil))
			      (setf dl-attribute-cell (cell (cell-link dl-attribute-cell))))))))))

  (defj J11 (a0 a1 a2) "ASSIGN (1) AS THE VALUE OF ATTRIBUTE (0) OF (2)"
	;; After J11, the symbol (1) is on the description list of
	;; list (2) as the value of attribute (0). If (0) was already
	;; on the description list, the old value has been removed,
	;; and (1) has taken its place; if the old value was local, it
	;; has been erased as a list structure (J72). If (0) is a new
	;; attribute, it is placed at the front of the description
	;; list. J11 will create the description list (with a local
	;; name) if it does not exist (head of (2) empty). There is no
	;; output in HO.
	(PopH0 3)
	(add-to-dlist (dlist-of (<== a2 :create-if-does-not-exist? t) :create-if-does-not-exist? t)
		      (<== a0)
		      ;; FFF ??? Maybe unrestrict this by auto-creating the cell?
		      (if (cell? a1) a1 (error "In J11, A1 has to be a cell, but it's ~s" a1)))
	)

  ;; It's sort of unclear, but (p. 179) seems to imply that these
  ;; remove the Hns: "Ten routines, J2 through J29, that provide block
  ;; transfers out of HO into working storage." Note: "out of H0"
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

  (defj J62 (target list-head-cell-or-its-name) "LOCATE (O) ONLIST (1)"
	;; LOCATE (0) ON LIST (1). A search of list with name (1) is made,
	;; testing each symbol against (0) (starting with cell after cell
	;; (1)). If (0) is found, the output (0) is the name of the cell
	;; containing it and H5 is set + . Hence, J62 locates the first
	;; occurrence of (0) if there are several. If (0) is not found,
	;; the output (0) is the name of the last cell on the list, and H5
	;; set - .  This is a bit of a problem, because the target could
	;; be a cell name or a string, which is ambiguous if we're handed
	;; a string. We heuristically see if the string can be a cell, in
	;; which case we use that cell's symb.
	(poph0 1)
	(let* ((inlink (if (cell? list-head-cell-or-its-name)
			   (cell-name list-head-cell-or-its-name)
			   (if (stringp list-head-cell-or-its-name)
			       list-head-cell-or-its-name
			       (break "J62 wants a cell name as the list entry to start at but got ~s"
				      list-head-cell-or-its-name))))
	       (incell (cell inlink))
	       (target (if (cell? target) (cell-symb target)
			   (if (stringp target)
			       (if (gethash target *symtab*) (cell target) 
				   target)
			       (break "J62 wants a string target but got ~s" target))))
	       )
	  (!! :jfns "J62 trying to locate target:~s in linear list starting with cell ~s~%" target incell)
	  (setf (H0) ;; The H5 has to be set in the subfn
		(j62-helper-search-list-for-symb target incell inlink))))

  (defj J63 (symbol-or-cell list-cell-or-name) "INSERT (0) BEFORE SYMBOL IN (1)"
	;; (1) is assumed to name a cell in a list. A new cell is
	;; inserted in the list behind (1). The symbol in (1) is
	;; moved into the new cell, and (0) is put into (1). The end
	;; result is that (0) occurs in the list before the symbol
	;; that was originally in cell (1).
	(let* ((list-cell (<== list-cell-or-name))
	       (new-cell-name (new-local-symbol))
	       (list-cell-symbol (cell-symb list-cell))
	       (new-cell (make-cell! :name new-cell-name :symb list-cell-symbol :link (cell-link list-cell)))
	       )
	  (if (cell? symbol-or-cell) (setf symbol-or-cell (cell-symb symbol-or-cell)))
	  (setf (cell-symb list-cell) symbol-or-cell
		(cell-link list-cell) new-cell-name))
	(poph0 2))

;;;	INSERT (0) AFTER SYMBOL IN (1). Identical with J63, except the symbol in (1) is left in (1), and (0) is put into the new cell, thus occurring after the symbol in (1). (If (1) is a private termination symbol, (0) is put in cell (1), which agrees with the definition of insert after.) 


  ;; WWW If this tries to work with numeric data there's gonna be a
  ;; problem bcs PQ will be wrong.
  (defj J65 (arg0 arg1) "INSERT (0) AT END OF LIST (1)"
	(PopH0 2)
	;; Identical to J66 except that it always inserts at the end
	;; of the list.
	(!! :jfns "J65 trying to append ~s to ~s~%" arg0 arg1)
	(loop with list-cell = (<== arg1)
	      with symb = (if (stringp arg0)
			      arg0
			      (if (cell? arg0)
				  (cell-symb arg0)
				  (break "Error in J66: ~a should be a symbol or cell!" arg0)))
	      do
	      (cond
		    ((zero? (cell-link list-cell))
		     (!! :jfns "J65 hit end, adding ~s to the list!~%" symb)
		     (let* ((new-name (new-local-symbol)) ;; (cell-name list-cell)))
			    ;; WWW If this tries to work with numeric data there's gonna be a problem!
			    (new-cell (make-cell! :name new-name :pq "21" :symb symb :link "0")))
		       (setf (cell-link list-cell) new-name)
		       (setf (cell new-name) new-cell)
		       (return t))))
	      ;; Move to next cell if nothnig above returned out
	      (setf list-cell (cell (cell-link list-cell)))))

  (defj J66 (arg0 arg1) "INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT"
	;; J66 INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT. A
	;; search of list (1) is made. against (0) (starting with the
	;; cell after cell (1) . If (0) is found, J66 does nothing
	;; further. If (0) is not found, it is inserted at the end of
	;; the list, as in J65. (??? What happens if the list
	;; branches??? At the moment this can't do anything sensible
	;; with a branching list!)
	(PopH0 2)
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
	(PopH0 2)
	(let* ((l0 (<== arg0))
	       (c1 (<== arg1))
	       (c1link (cell-link c1))
	       (last-cell-in-l0 (last-cell-of-linear-list l0)))
	  (cond ((zero? (cell-link l0))
		 (vv (h0) c1)
		 (setf (h5) "-"))
		(t (setf (cell-link c1) (cell-link l0))
		   (setf (cell-link last-cell-in-l0) c1link)
		   (vv (h0) last-cell-in-l0)))))

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
	(PopH0 2) ;; WWW ???
	(!! :jfns "J100 GENERATE SYMBOLS FROM LIST ~s FOR SUBPROCESS ~s~%" arg1 arg0)
	(loop with cell-name = (cell-link (<== arg1))
	      with cell
	      with exec-cell = (make-cell! :symb arg0 :link "0")
	      until (zero? cell-name)
	      do ;; FFF %%% There's a mofit here that could be
		 ;; captured in a macro, of getting the name to check
		 ;; for zero? and then when it's not zero, getting the
		 ;; cell.
	      (setf cell (cell cell-name))
	      ;; Push the arg
	      (vv "H0" (cell-symb cell))
	      (setf (H5) "+")
	      ;; Call the routine
	      (!! :jfns "J100 is applying ~s to ~s~%" arg0 (H0))
	      ;; Unfortunately, ipl-eval needs a start cell. If we are
	      ;; given a symbol here, we need to wrap it in a dummy
	      ;; execution cell with an immediate pop.
	      (ipl-eval exec-cell)
	      ;; Pop the arg
	      (^^ "H0") 
	      ;; Move to next cell (name)
	      (setf cell-name (cell-link cell))
	      ))

  (defj J111 (arg0 arg1 arg2) "(1) - (2) -> (O)."
	;; The number (0) is set equal to the algebraic difference between numbers
	;; (1) and (2). The output (0) is the input (0).
	;; *** WWW (PopH0 2) -- Ackermann fails if this gets done!!! *** WWW
	;;     and it's unclear how to do is anyway, because it says it changes (0) *** ???
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
	;; COPY (0). The output (0) names a new cell containing the
	;; identical contents to (0). The name is local if the input
	;; (0) is local; otherwise, it is internal.
	;; (No pop bcs H0 is replaced -- Maybe pop and push?)
	(let* ((old-cell (<== (H0)))
	      (new-cell (copy-cell old-cell))
	      (new-name (new-local-symbol)))
	  (setf (cell-name new-cell) new-name)
	  (!! :jfns "Copied ~s -> ~s into H0.~%" old-cell new-cell)
	  (store new-cell)
	  ;; WWW Some code seems to want the copy to push the old H0,
	  ;; but the doc doesn't say that this does a push. ???
	  (setf (H0) new-cell)))

  (defj J124 () "CLEAR (0)"
	;; The number (0) is set to be 0. If the ce 1is not a data term, it is
	;; made an in- teger data term= 0. If a number, its type, integer, or
	;; floating point, is unaffected. It is left as the output (0).
	;; (No pop bcs H0 is replaced -- Maybe pop and push?)
	(let ((H0 (<== (H0))))
	  (!! :jfns "J124: Clear (H0): ~s~%" H0)
	  (setf (cell-link H0) 0)))

  (defj J125 () "TALLY 1 IN (0)"
	;; An integer 1 is added to the number (0). The type of the result
	;; is the same as the type of (0). It is left as the output
	;; (0). [NNN: If there is no value in (0) this assumes zero and
	;; set the number to 1"
	;; (No pop)
	(let* ((H0 (<== (H0)))
	       (curval (cell-link H0)))
	  (!! :jfns "J125: Tally (H0) currently: ~s~%" H0)
	  (setf (cell-link H0)
		(if (not (numberp curval))
		    (progn (!! :jfns "Warning! J125 was send a non-number: ~s, setting result to 1~%" curval) 1)
		    (1+ curval)))))

  (defj J130 (H0) "TEST IF (O) IS REGIONAL SYMBOL"
	;; Tests if Q = 0 in H0.
	;; No Pop H0
	(if (zerop (getpq :q (cell-pq (<== H0))))
	    (setf (H5) "+") (setf (H5) "-")))

  (defj J136 (H0) "MAKE SYMBOL (O) LOCAL."
	;; The output (0) is the input (0) with Q = 2. Since all
	;; copies of this symbol carry along the Q value, if a symbol
	;; is made local when created, it will be local in all its
	;; occurrences. [I have no idea what his last sentence means!]
	;; (No pop bcs H0 is modified)
	(let ((cell (<== H0 :create-if-does-not-exist? t)))
	  (setf (cell-pq cell)
		(let* ((pq (cell-pq cell))
		      (l (length pq)))
		  (case l
		    (0 "02")
		    (1 (!! :jfns "Warning: J136 assuming ~s is q-only!%") "02")
		    (2 (setf (aref pq 1) #\2) pq)
		    (t (Error "In J136 got ~s for pq in ~s" pq cell)))))
	  (setf (H0) cell)))

  (defj J148 () "MARK ROUTINE (0) TO PROPAGATE TRACE."
	;; Identical to J147, except uses Q = 4.
	;; Pop????
	(!! :jfns "J148 (MARK ROUTINE (0) TO PROPAGATE TRACE.) is a noop."))

  ;; Input and output are completely kludged, and unlike in original IPL. Partly
  ;; this is required because we don't have the same sort of physical
  ;; environment. There are tapes, and so on. But also, partly it's for
  ;; kludge-convenience. For example, there is exactly one 80 column
  ;; input/output buffer and it's used for all input and output.

  (defj J151 (arg0) "Print list (0)"
	(PopH0 1)
	(line-print-linear-list arg0))

  (defj J152 () "PRINT SYMBOL (0)"
	;; Pop after!!
	(line-print-cell (H0))
	(PopH0 1))

  (defj J154 () "Clear print line"
	;; Clear Print Line CLEAR PRINT LINE. Print line 1W24 is cleared and the
	;; current entry column, 1W25, is set equal to the left margin, 1W21 [always 1 at the moment].
	(setf *W24-Line-Buffer* (blank80))
	(setf (cell-link (cell "W25")) 0))

  (defj J155 () "Print line"
	(!! :io "J155 Print Line vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv~%")
	(format t "~a~%" *W24-Line-Buffer*)
	(!! :io "J155 Print Line ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^~%")
	)

  (defj J157 (a0) "ENTER DATA TERM (0) LEFT-JUSTIFIED"
	;; Data term (0) is entered in the current print line with its
	;; leftmost character in print position 1W25, 1W25 is
	;; advanced, and H5 is set + . If (0) exceeds the remaining
	;; space, no entry is made and H5 is set - .
	(poph0 1)
	(!! :jfns "J157 called on ~s~%" a0)
	(let* ((s (cell-symb (<== a0)))
	       (l (length s))
	       (p (cell-link (cell "W25"))))
	  (when (> (+ l p) 80) (setf (H5) "-") (return nil))
	  (loop for c across s
		as i from p by 1
		do (setf (aref *W24-Line-Buffer* i) c))
	  (setf (cell-link (cell "W25")) (+ l p) ;; !!!!!!! WWWWWW OBIWAN !!!!!!!!
		(H5) "+")))

  (defj J161 (a0) "INCREMENT COLUMN BY (0)"
	;; (0) is taken as the name of an integer data term. Current
	;; entry column, 1W25, is set equal to 1W25 + (0).
	(poph0 1)
	(let ((w25 (cell "W25")))
	  (setf (cell-link w25) (+ (cell-link (<== a0)) (cell-link w25)))))
  
  (defj J180 () "READ LINE J180 READLINE"
	;; The next record on unit 1W18 is read to line 1W24. (The record is
	;; assumed to be BCD, 80 cols.) Column 1 of the record is read into
	;; column 1 of the read line, and so forth. H5 is set+. If no record can
	;; be read (end-of-file condition), the line is not changed and H5 is
	;; set - . [Note that 1W24 is ignored here and the input is put into our
	;; global single-line store: *W24-Line-Buffer*. Also, we set W25, the read
	;; position to numerical 1.]
	(let ((line (read-line *input-stream* nil nil)))
	  (!! :io "J180 Read: ~s~%" line)
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
	  ;; Note that, unlike J182, here "All non-numerical
	  ;; characters except in the first column are ignored." So we
	  ;; need a special scraping step to carry this out.
	  (setf string (j181-helper-remove-non-numeric-except-first string))
	  (!! :jfns "J181 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a]~%" string start end *W24-Line-Buffer* w25p w30n)
	  (incf (cell-link w25) w30n) 
	  (if (j181-helper-is-regional-symbol? string)
	      (progn
		(!! :jfns "J181 decided that ~s IS a regional symbol, so we're installing it.~%" string)
		(make-cell! :name string)
		(setf (H0) string) (setf (H5) "+"))
	      (progn
		(!! :jfns "J181 decided that ~s is NOT a regional symbol.~%" string)
		(setf (H5) "-")))))

  (defj J182 (arg0) "INPUT LINE DATATERM (0)"
	;; Pop???
	;; J182 INPUT LINE DATA TERM (0). The field specified as J181
	;; is taken as the value of a data term. Input data term (0)
	;; is set to that value and left as output (0). H5 is set +.
	;; The data type of input (0) determines the data type of the
	;; output. If the input (0) is a decimal or octal integer, or
	;; BCD, the read line field is interpreted as that type. Any
	;; other data type is treated as BCD. In composing BCD data
	;; terms, the field is left-justified and the full data term
	;; completed with blanks on the right, if necessary. If the
	;; specified field exceeds five columns, the rightmost five
	;; columns are taken as the field. In composing decimal and
	;; octal integer data terms, non-numerical charac-ters are
	;; ignored. If the resulting information exceeds the capacity
	;; of the data term, the rightmost digits are retained. If the
	;; read line field is entirely blank (or non-numerical, for
	;; integer data types), (0) is cleared (to blanks for BCD; to
	;; zero for integer) and H5 is set - . In either case, 1W25 is
	;; incremented by the amount 1W30.
	(let* ((w25 (cell "W25"))
	       (w25p (cell-link w25))
	       (w30 (cell "W30"))
	       (w30n (cell-link w30))
	       (start (- (1+ w25p) 2))
	       (end (+ 1 start w30n))
	       (string (subseq *W24-Line-Buffer* start end)))
	  ;; WWW Assumes that the target is alpha, which could be wrong in future applications!
	  (setf (cell-symb arg0) string)
	  (incf (cell-link w25) w30n)
	  (!! :jfns "J182 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a] and jammed it into ~s~%" string start end *W24-Line-Buffer* w25p w30n arg0)
	))

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
 
  (defj J184 (arg0) "SET (0) TO NEXT NON-BLANK"
	;; J184 SET (0) TO NEXT NON-BLANK. Same as J183, except scans for any
	;; non-blank character.
	(J183/4-Scanner arg0 :non-blank))

  (defj J186 () "INPUT LINE CHARACTER"
	;; The character in column 1W25 of line 1W24 is input to HO,
	;; H5 is set +. If the character is numerical, that internal
	;; symbol is input; if the character is non-numerical, the
	;; zeroth symbol in the region designated by that character is
	;; input; i.e., A->AO, 3->3. If the character is a blank,
	;; there is no input and H5 is set - In either case, 1W25 is
	;; not advanced.
	(let* ((c (aref *W24-Line-Buffer* (1- (cell-link (cell "W25"))))))
	  (!! :jfns "J186 read ~s~%" c)
	  (if (char-equal #\space c)
	      (setf (H5) "-")
	      (setf (H0) (make-cell! :name (new-local-symbol)
				     :symb (format nil (if (numchar? c) "~c" "~c0") c))
		    (H5) "+"))))

  (defj J71 () "Unimplemented!" (break "J71 is unimplemented!"))
  (defj J72 () "Unimplemented!" (break "J72 is unimplemented!"))
  (defj J160 () "Unimplemented!" (break "J160 is unimplemented!"))
  (defj J116 () "Unimplemented!" (break "J116 is unimplemented!"))
  (defj J7 () "Unimplemented!" (break "J7 is unimplemented!"))
  (defj J14 () "Unimplemented!" (break "J14 is unimplemented!"))
  (defj J133 () "Unimplemented!" (break "J133 is unimplemented!"))
  (defj J18 () "Unimplemented!" (break "J18 is unimplemented!"))
  (defj J68 () "Unimplemented!" (break "J68 is unimplemented!"))
  (defj J17 () "Unimplemented!" (break "J17 is unimplemented!"))
  (defj J19 () "Unimplemented!" (break "J19 is unimplemented!"))
  (defj J75 () "Unimplemented!" (break "J75 is unimplemented!"))
  (defj J78 () "Unimplemented!" (break "J78 is unimplemented!"))
  (defj J138 () "Unimplemented!" (break "J138 is unimplemented!"))
  (defj J137 () "Unimplemented!" (break "J137 is unimplemented!"))
  (defj J115 () "Unimplemented!" (break "J115 is unimplemented!"))
  (defj J114 () "Unimplemented!" (break "J114 is unimplemented!"))
  (defj J126 () "Unimplemented!" (break "J126 is unimplemented!"))
  (defj J15 () "Unimplemented!" (break "J15 is unimplemented!"))
  (defj J166 () "Unimplemented!" (break "J166 is unimplemented!"))
  (defj J1 () "Unimplemented!" (break "J1 is unimplemented!"))
  (defj J79 () "Unimplemented!" (break "J79 is unimplemented!"))
  (defj J156 () "Unimplemented!" (break "J156 is unimplemented!"))
  (defj J110 () "Unimplemented!" (break "J110 is unimplemented!"))
  (defj J147 () "Unimplemented!" (break "J147 is unimplemented!"))

  )




;;; ===================================================================
;;; JFn Utilities

;;; Used to pop the inputs of JFns. Usually you'll want to do this
;;; before the operation because you'll often want to put a result
;;; back on. Unfortunately, it's not consistent whether a jfn removes
;;; all its args.

(defun PopH0 (n) (dotimes (i n) (^^ "H0")))

(defparameter *LT-Regional-Chars* "ABCDEFGIKLMNOPQRSTUVXYZ-*=,/+.()'")

(defun add-to-dlist (dlisthead att valcell &key (if-aleady-exists :replace)) ;; :error :allow-multiple
 (!! :jfns "ADD-TO-DLIST entry: dlisthead = ~s, att=~s, valcell = valcell=~s~%" dlisthead att valcell)
 (loop with dlist-name = (cell-name dlisthead)
       with valcell-name = (cell-name valcell)
       with attname = (if (stringp att) att
			  (if (cell? att) (cell-name att)
			      (error "In ADD-TO-DLIST, att must be a string or cell, but is ~s" att)))
       with next-att-cell = (cell-link dlisthead)
       with last-val-cell = dlisthead ;; In case we fall through immediately
       until (zero? next-att-cell)
       do
       (setf next-att-cell (cell next-att-cell)) ;; Can't do this above bcs need zero? check
       (!! :jfns "ADD-TO-DLIST is checking next-att-cell=~s, last-val-cell=~s~%"
	   next-att-cell last-val-cell)
       (if (string-equal attname (cell-symb next-att-cell))
	   (case if-aleady-exists
	     (:replace (setf (cell-link next-att-cell) valcell-name) (setf (H5) "+") (return t))
	     (:error (error "In ADD-TO-DLIST, att ~a already exits in ~s" att dlisthead))
	     (:allow-multiple nil) ;; When we get to the end we'll add a new one.
	     ))
       (let* ((val-link (cell-link next-att-cell)))
	 (if (blank? val-link)
	     (error "In ADD-TO-DLIST, att ~a has no value in ~a" next-att-cell dlisthead))
	 (setf last-val-cell (cell val-link))
	 (setf next-att-cell (cell-link last-val-cell)))
       finally
       ;; If we got here we're holding the last val in last-val-cell
       ;; and need to append the new att and val. The one edge case
       ;; is if there are not atts at all, in which case
       ;; last-val-cell will be dlisthead ... which I hope is right!
       (let*
	   ((val-linking-cell (make-cell! :name (new-local-symbol dlist-name) :symb valcell-name :link "0"))
	    (new-att-cell (make-cell! :name (new-local-symbol dlist-name) :symb attname :link (cell-name val-linking-cell))))
	 (!! :jfns "ADD-TO-DLIST taking the finally option: last-val-cell=~s, val-linking-cell=~s, new-att-cell = ~s~%"
	     last-val-cell val-linking-cell new-att-cell)
	 (setf (cell-link last-val-cell) (cell-name new-att-cell))
	 (setf (H5) "+")
	 (return t)))
  )

(defun dlist-of (listhead &key (create-if-does-not-exist? nil))
  (let* ((dlisthead (cell-symb listhead)))
    (if (not (zero? dlisthead)) (cell dlisthead)
	(if (not create-if-does-not-exist?)
	    (error "DLIST-OF wants there to already be a dlist in ~s" listhead)
	    (let* ((dlname  (new-local-symbol (cell-name listhead)))
		   (dlhead (make-cell! :name dlname :symb "0" :link "0")))
	      (setf (cell-symb listhead) dlname)
	      dlhead)))))
	      
;;; This'd be a LOT simpler on a linear list! In fact, let's just
;;; assume that it's a linear list for now until proved
;;; otherwise. It'd be hard to tell what the meaning of "search" is on
;;; a non-linear list.

(defun j62-helper-search-list-for-symb (target-symb incell inlink)
  (loop until (zero? inlink)
	do 
	(when (string-equal (cell-symb incell) target-symb)
	  (setf (H5) "+")
	  (return inlink))
	(setf inlink (cell-link incell) incell (cell inlink))
	finally (progn (setf (H5) "-") (return incell))))

  #|

  This was an attempt to do this on a tree:

  (if (zero? inlink) (progn (setf (H5) "-") inlink)
      (let* ((incell (cell inlink)))
	(if (string-equal (cell-symb incell) target-symb)
	    (cell-name incell)
	    ;; Here's where it'd be useful to know when something is a data cell!
	    (or (let ((r (j62-helper-search-list-for-symb target-symb (cell-symb incell))))
		  (when r (setf (H5) "+") r))
		(let ((r (j62-helper-search-list-for-symb target-symb (cell-link incell))))
		  (j62-helper-search-list-for-symb target-symb (cell-symb incell)))))))
|#

(defun j181-helper-remove-non-numeric-except-first (s)
  (let* ((r (copy-seq " ")))
    (setf (aref r 0) (aref s 0))
    (loop as p from 1 to (1- (length s))
	  as c = (aref s p)
	  do (if (numchar? c)
		 (setf r (format nil "~a~c" r c)))
	  finally (return r))))

(defun numchar? (c)
  (find c "0123456789"))

(defun j181-helper-is-regional-symbol? (string)
  (and (find (aref string 0) *LT-Regional-Chars*)
       (loop for p from 1 by 1
	     with lim = (1- (length string))
	     until (= p lim)
	     if (not (find (aref string p) "0123456789"))
	     do (return nil)
	     finally (return t))))

(defun num?get (sym)
  (let* ((cell (<== sym))
	 (n (cell-link cell)))
    (if (numberp n) n
	(break "In ~a, asked to test a non-number: ~s from ~s (~s)." n cell sym))))
    
;;; !!! WWW OBIWAN UNIVERSE WITH LISP ZERO ORIGIN INDEXING WWW !!!
;;; (NNN H0p might be deprecated FFF Remove?)

(defun J183/4-Scanner (arg0 mode)
  (let* ((H0 (<== arg0))
	 (w25p (cell-link (cell "W25")))
	 ;;(h0p (cell-link H0))
	 )
    (!! :jfns "Starting in J183/4-Scanner: H0 = ~s, w25p = ~a, h0p = ~%" H0 w25p) ;; h0p)
    ;; (if (not (numberp h0p)) (break "In J183/4 expected H0(p) (~a) to be a number.~%" (H0)))
    (if (not (numberp w25p)) (break "In J183/4 expected W25(p) (~a) to be a number.~%" (cell "W25")))
    (setf (H5) "-")
    (incf w25p)		    ;; Start at W25+1 (per manual)
    (loop until (= w25p 80) 
	  ;; WWW OBIWON !!! The only place I should have to correct this is here (I hope!) 
	  as char = (aref *W24-Line-Buffer* (1- w25p))
	  do 
	  (!! :jfns "Deep in J183/4-Scanner: w25p = ~a, char = ~s, h0p = ~%" w25p char) ;; h0p)
	  (when (case mode
		  (:blank (char-equal char #\space))
		  (:non-blank (not (char-equal char #\space)))
		  (t (error "!!! J183/4-Scanner given unknown mode: ~s" mode)))
	    ;;(setf (cell-link H0) h0p)
	    (setf (cell-link H0) w25p)
	    (setf (H5) "+")
	    (return t))
	  ;; (incf H0p)
	  (incf w25p)
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
	do (setf (cell (format nil "W~a" nn)) val))
  (PopH0 n))

(defun J3n=restore-wn (n)
  (loop for nn from 0 to n do (^^ (format nil "W~a" nn))))

(defun J4n=preserve-wn (n)
  (loop for nn from 0 to n do (vv (format nil "W~a" nn))))

(defun J5n=preserve-wn-then-move-0-n-into-w0-wn (n)
  (J4n=preserve-wn n)
  (J2n=move-0-to-n-into-w0-wn n)
  )

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
  (format t "~%+--------------------- ~s ---------------------+~%" cell)
  ;; FFF Maintain depth and indent.
  (when (not (zero? (cell-symb cell)))
      (format t "| Description list:~%")
      (line-print-linear-list (cell-symb cell))
      (format t "| End of description list~%| ---------------------~%"))
  (loop do (format t "| ~s~70T|~%" cell)
	(let ((link (cell-link cell)))
	  (if (zero? link) (return :end-of-list))
	  (setf cell (cell link))))
  (format t "+---------------------------------------------------------------------+~%")
  )
(defun lpll (c) (line-print-linear-list c))

(defun line-print-cell (cell)
  (setf cell (<== cell))
  (format t "~%+--------------------- ~s ---------------------+~%" cell)
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
  (!! :run "vvvvvvvvvvvvvvv Entering IPL-EVAL at ~s~%" start-cell)
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
	 (when *fname-hint* 
	   (!! :run (if arglist ">>>>>>>>>> Calling ~a [~a]~%   ~s=~s~%"
			">>>>>>>>>> Calling ~a [~a] (No Args)~*~*~%")
	       *fname-hint* (getf (gethash *fname-hint* *jfn-plists*) 'explanation) arglist args)
	   (maybe-break? *fname-hint*)
	   (setf *fname-hint* nil)
	   )
	 (apply (H1) args))
       (^^ "H1") ;; Remove the JFn call
       (go ADVANCE)
       )
     (setq cell (H1)) ;; This shouldn't be needed since we're operating all in cell now.
     (!! :run ">>>>>>>>>> Executing: ~s (~a)~%" cell *adv-limit*)
     (maybe-break? (cell-id cell))
     (setf *trace-instruction* cell) ;; For tracing and error reporting
     (setf pq (cell-pq cell)
	   q (getpq :q pq)
	   p (getpq :p pq)
	   symb (cell-symb cell)
	   link (cell-link cell)
	   )
     (!! :run-full "-----> At INTERPRET-Q: CELL =~s~%      Q = ~s, symb=~s~%" cell q symb)
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
       (6 ;; Copy (0) in S -- opposite of 5, and we unpack the cell to a symbol.
	(setf (cell (s)) (cell-symb (<== (H0)))))
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
     (trace-cells)
     (if (and *adv-limit* (zerop (decf *adv-limit*)))
	 (break " !!!!!!!!!!!!!! IPL-EVAL hit *adv-limit* !!!!!!!!!!!!!!~%"))
     (incf (cell-link (cell "H3")))
     (when (string-equal (cell-symb (h1)) "exit")
       (!! :run "Exiting from IPL-EVAL ^^^^^^^^^^^^^^^~%")
       (return))
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (cell-link (H1)))
   ADVANCE-W/FORCED-LINK (!! :run-full "-----> At ADVANCE-W/FORCED-LINK (link=~s)~%" link)
     (setf *fname-hint* link)
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
     (trace-cells)
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

(defun first-n (n l) (loop for i below n as e in l collect e))

(defun core-dump (table)
  (format t "~a contains ~a entries:~%" table (hash-table-count table))
  (loop for key being the hash-keys of table
	using (hash-value value)
	do (format t "~s => ~s~%" key value)))

(defun maybe-break? (s)
  (when (or (equal t *breaks*)
	    (member t *breaks*)
	    (member s *breaks* :test #'string-equal))
    (break "************************** Break called by user at ~s (BEFORE execution!)" s)
    (report-system-cells)))

;;; =========================================================================
;;; Test calls

;;; rsc rsc* (lpll cell)

(untrace)
(setf *trace-cell-names* nil)
(setf *stack-depth-limit* 100) ;; FFF ? Localize ?
(setf *!!list* '()) ;; :deep-memory :load :run :jfns :run-full :io :end-dump (t for all)

(progn ;; Just quote this line to suppress these tests
  (setf *!!list* '()) ;; :deep-memory :load :run :jfns :run-full :io :end-dump (t for all)
  (load-ipl "F1.lisp")
  (trace ipl-eval)
  (load-ipl "Ackermann.iplv" :adv-limit 100000)
  (print (cell "N0"))
  (if (= 61 (cell-link (cell "N0")))
      (format t "~%*********************************~%* Ackerman (3,3) = 61 -- Check! *~%*********************************~%")
      (error "Oops! Ackermann (3,3) should have been 61, but was ~s" (cell "N0")))
  )

(untrace)
(setf *!!list* '(:run :jfns)) ;; :deep-memory :load :run :jfns :run-full :io :end-dump (t for all)
(defun step! () (setf *breaks* t) "Use :c to step.")
(defun free! () (setf *breaks* nil) "Use :c to run free.")
(setf *breaks* '()) ;; If this is set to t (or '(t)) it break on every call
;(trace add-to-dlist dlist-of)
(setf *trace-cell-names* '("W0" "W1" "H0"))
(load-ipl "LTFixed.lisp" :adv-limit 10000)

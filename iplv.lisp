;;; (load (compile-file "iplv.lisp"))

(setf *print-pretty* nil)

#|

www Local symbols in our case are ROUTINEID-9-... and get created at
load time. Some of the code tests for a local symbol by knowing that
the 9- is at the head, which is NOT true (it could test for a 9- at
the head, or a 9- anywhere, or a name + -9- ...) Maybe localization
should be done by pure 9- gensym, but then it would be impossible to
f'ing figure out what routine something is in. ... ??? This is going
to come back to bite us! (see convert-local-symbols)

FFF H3 cycle counter sometimes doesn't incremement. It's probably
incf'ed in a slightly wrong place, but I'm not changing it now bcs I'm
in the middle of debugging something.

WWW (from J136): "all copies of this symbol carry along the Q
value..."!!!

FFF Consider replacing system cells stacks with JUST symbols, thus
avoiding entirely the mess of accidently sharing and destructive
disasters.

WARNING WARNING WARNING! THIS LANGUAGE HAS SO MANY RANDOM POTHOLES!!!
The weirdest example (so far) is that the symbol "P" is actually the
0th cell in the P zone, so is really "P0", so that all the code that
handles things like finding the list P needs to be able to understand
that P0 is really referring to "P". Ugh. (See manual p. 13 (prob. 4),
215, and 237 (J186). UGH UGH UGH. (The way I get around this is
to "fix" the singlton letters in the original code, so that the name,
for example, A goes to A0.

(Note the J8 error popping stack motif!)

It seems that all JFns will remove their inputs, e.g., p.10: "...it is
understood from the definition of TEST that J2 will remove both (0)
and (1) from HO." UNLESS OTHERWISE STATED! See: (PopH0 n) FFF ???
Maybe fold poph0, to the extent possible, into DefJ?

WWW Noting handles multiply-nested dlists!

WWW A lot of code assumes that a list isn't branching -- e.g., DLIST
processing.

??? Does anyone need W24 (read/print line) to be an actual cell?
Right now it's a special global that can only process on line of I or
O at a time.

WWW WATCH OUT FOR memory leaks are that are leaving junk on the
stacks (primarily H0) ... usually it's the Jfns that aren't cleaning
up after themselves, and/or not absorbing their inputs. Also WATCH OUT
FOR accidental pointer sharing -- failing to copy. AVOID SETF'inf into
cells -- use ipop and ipush almost always!

WWW There's a hack for true blanks in both symb and link in
LT:/016D070 to avoid the load-time trap. Eventually (FFF) test for
data mode 21 to allow both blanks.

WWW If J65 tries to insert numeric data there's gonna be a problem bcs
PQ will be wrong. (I don't deeply understand the numerical data
representation. For example, there NO handling of floats in the
current system.)

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
(defun cell? (cell?) (eq 'cell (type-of cell?)))

(defvar *symtab* (make-hash-table :test #'equal))
(defvar *systacks* (make-hash-table :test #'equal))

(defun newsym (&optional (prefix "9")) (string (gensym (concatenate 'string prefix "+"))))

(defmacro make-cell! (&rest args)
  `(store (make-cell ,@args)))

(defmacro !! (key &rest args) 
  `(when (or (equal *!!* t)
	     (equal ,key t)
	     (member ,key *!!*))
     ,(if (stringp (car args))
	  `(format t ,(car args) ,@(cdr args))
	  `(progn ,@args))))

(defun store (cell &optional (name (cell-name cell)))
  (!! :dr-memory "== Store ==> ~s [mem]~%" cell)
  (setf (gethash name *symtab*) cell)
  cell)
  
(defun zero? (what) (if (stringp what) (member what '("" "0") :test #'string-equal)))

(defun blank? (what)
  (string-equal "" what))

(defun print-cell (cell s d)
  (declare (ignore d))
  (format s "{~a~a|~a|~a|~a~a}"
	  (if (zero? (cell-id cell)) "" (format nil "~a::" (cell-id cell)))
	  (cell-name cell)
	  (cell-pq cell)
	  (cell-symb cell)
	  (cell-link cell)
	  (if (and (zero? (cell-comments cell)) (zero? (cell-comments.1 cell))) 
	      ""
	      (format nil " [~a;~a]" (cell-comments cell) (cell-comments.1 cell)))))

;;; The generator triplex. The generator system maintains its own
;;; private stack, which is the "generator hideout" referred to in the
;;; manual and below where J17-19 are defj'ed.

(defvar *genstack* nil)
(defstruct gentry fn wn wnames +-) 

;;; =========================================================================
;;; DEBUGGING UTILS

(defvar *trace-instruction* nil) ;; Used in error traps, so need to declare early.
(defvar *fname-hint* "") ;; for messages in the middle of jfn ops
(defvar *jfn-calls* (make-hash-table :test #'equal))

(defun rj () ;; report on jfns
  (let ((*print-length* nil))
    (loop for (jname ncalls expl argcounts) in 
	  (sort 
	   (loop for jname being the hash-keys of *jfn-calls*
		 using (hash-value args)
		 as calls = (loop for al in (uniquify-list args)
				  collect (cons (or al :noargs)
						(count al args :test #'equal)))
		 collect (list jname
			       (reduce #'+ (mapcar #'cdr calls))
			       (getf (gethash jname *jfn-plists*) 'explanation)
			       (sort calls #'> :key #'cdr)))
	   #'> :key #'second)
	  do (format t "~a ~a [~a]~%   ~a~%" ncalls jname expl argcounts))))

(defvar *card-ids-executed* nil)
(defvar *rxtbl* (make-hash-table :test #'equal))
(defun rx () ;; report on execs (card ids executed)
  (clrhash *rxtbl*)
  (loop for id in *card-ids-executed*
	if (and (stringp id) (= 8 (length id)))
	do (incf (gethash (subseq id 0 4) *rxtbl* 0)))
  (mapcar #'print
	  (sort 
	   (loop for rname being the hash-keys of *rxtbl*
		 using (hash-value nx)
		 collect (cons rname nx))
	   #'string< :key #'car)))

(defvar *cell-tracing-on* nil)
;;; These will get eval'ed at the given id, for example:
;;;   ("P051R050" (print "hello"))
;;; or, more reasonably:
;;; ("P051R050" (setf *trace-cell-names* '("W0" "W1" "H0" "H5") *cell-tracing-on* t))
;;; If the ID is a number rather than a string, it refers to the value in (H3)
(defvar *trace-@orID-exprs* nil) 
(defvar *breaks* nil) ;; If this is set to t it breaks on every call
(defvar *trace-cell-names* nil) 

;;; t for all or :dr-memory :load :run :jdeep :run-full :io :end-dump 
;;; :deep-alerts :pq
(defvar *!!* nil) 
(defparameter *default-!!list* '(:run :jcalls))

(defun step! () (setf *breaks* t) "Use :c to step.")
(defun free! (&optional next-breaks) (setf *breaks* next-breaks) "Use :c to run free.")

(defun ds () ;; dump-stack
  (loop for key being the hash-keys of *systacks*
	using (hash-value val)
	do (print (list key val)))
  (format t "~%~%") :done)

;;; =========================================================================
;;; ACCESSORS

;;; Cell dereferencing: Used when you need a cell. <=! is more
;;; powerful in that it can create the cell if it's not found, and is
;;; slightly heuristic. <== should be used where possible, and only
;;; use <=! when you need the heuristication and/or auto-creation.

(defun <== (cell-or-symb)
  (!! :dr-memory "<== retreiving ~s~%" cell-or-symb)
  (if (cell? cell-or-symb) cell-or-symb (gethash cell-or-symb *symtab*)))

(defun <=! (cell-or-symb &key create-if-does-not-exist?) ;; cell-or-symb can be a cell or a name
  (!! :dr-memory "<=! retreiving ~s~%" cell-or-symb)
  (or (<== cell-or-symb)
      (if (stringp cell-or-symb)
	  (if create-if-does-not-exist?
	      (let ((new-cell (make-cell! :name cell-or-symb)))
		(!! :dr-memory "<=! created ~s~%" new-cell)
		new-cell)
	      (error "In <=! ~s isn't a cell and you didn't ask to create it!"
		     cell-or-symb)))))

(defmacro cell-name% (cell-or-symb)
  `(cell-name (<== ,cell-or-symb)))
(defmacro cell-symb% (cell-or-symb)
  `(cell-symb (<== ,cell-or-symb)))

;;; Dereferencing versions of cell struct accessors. Cell is macro for
;;; stacked symbols, like H0 and W0, used where there isn't a special
;;; macro for common ones.  WWW Note the convention of adding + when
;;; the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot
;;; try to push/pop things that aren't stacks!

(defmacro cell (symb) `(gethash ,symb *symtab*))
(defmacro stack (symb) `(gethash ,symb *systacks*)) ;; Only system cells have stacks

;;; Important values have special macros (these are like (H0) = (0) in
;;; the IPL-V manual). The ...+ fns return the whole stack. (Note that
;;; you'll have to get (1), that is, the second stack entry in H0
;;; manually!)

(defmacro H0 () `(cell "H0"))
(defmacro H0+ () `(stack "H0"))

;;; Input/Push to system stack: This creates a copy only of the
;;; CONTENTS of the system cell.

;;; WWW DESTRUCTIVE!!! MAKE SURE YOU'RE DOING IT TO A CLEAN CELL!!!
(defun data-set (curcell &key (sign "0") (pq "0") (symb "") (link "0") (id ""))
  (!! :dr-memory "WWW DATA-SET IS DESTRUCTIVELY HACKING ~s " curcell)
  (setf (cell-sign curcell) sign
	(cell-pq curcell) pq
	(cell-symb curcell) symb
	(cell-id curcell) id
	(cell-link curcell) link
	)
  (!! :dr-memory " TO: ~s~%" curcell)
  curcell)

;;; WWW *** Note that the stacked cells are NOT stored in the symbtab
;;; -- only the main is! (We use "make-cell" NOT "make-cell!"; In fact,
;;; they don't have names!)  (FFF Maybe use hiearchical structs to
;;; separate the load from the cell name?)

(defun ipush (stack-name &optional newval)
  (!! :dr-memory "IPUSH wants to put ~s on ~a~%" (or newval "[nil: No newval]") stack-name)
  ;; Start by creating a new cell on the stack and copy everything from
  ;; the main cell into it. NOTE THAT THIS IS NOT SAVED!
  (let* ((topcell (cell stack-name))) 
    (push (make-cell :sign (cell-sign topcell)
		     :pq (cell-pq topcell)
		     :symb (cell-symb topcell)
		     :link (cell-link topcell))
	  (stack stack-name))
    ;; Now create another new cell, this time to replace the top cell. This one IS saved!
    (let ((newmain (store (copy-cell topcell)))) ;; NNN WWW This will replace the top cell in the symbtab!
      ;; And replace it with whatever it appropriate given the input type.
      (cond ((or (stringp newval) (functionp newval))
	     (data-set newmain :symb newval))
	    ((cell? newval)
	     ;; Here we copy everything into it (except the name).
	     (data-set newmain :sign (cell-sign newval) :pq (cell-pq newval) :symb (cell-name newval) :link (cell-link newval))
	     (!! :run-full "iPushing a copy of data from ~s on ~a~%" newval stack-name))
	    ((null newval)
	     ;; This is just a push, and the copy has already been made.
	     (!! :run-full "iPushing ~a~%" stack-name))
	    ((numberp newval)
	     (!! :run-full "iPushing (the number) ~s on ~a~%" newval stack-name)
	     (data-set newmain :pq "12" :link newval))
	    (t (break "IPUSH asked to push ~s onto ~a~%" newval stack-name)))
      (!! :dr-memory "IPUSH pushew new cell: ~s (WWW NOT STORED!) on ~s~%" newmain stack-name)
      newmain)))

;;; Warning: Pop has to create a new cell in the head otherwise anyone
;;; holding the old value might have it destroyed. (Actually, I think
;;; that this is safe bcs all pushes create new cells, but better
;;; clean than worry.)

(defun ipop (stack-name)
  (let* ((popped-cell (pop (stack stack-name)))
	 (new-cell (make-cell!
		    :name stack-name
		    :pq (cell-pq popped-cell)
		    :symb (cell-symb popped-cell)
		    :link (cell-link popped-cell)
		    :id (cell-id popped-cell))))
    (!! :dr-memory "IPOP created new cell: ~s on ~a, popping ~s~%" new-cell stack-name popped-cell)
    new-cell
    ))

;;; This is used in JFns to deref args H0

(defmacro H1 () `(cell "H1")) ;; WWW DO NOT CONFUSE H1 with (1) !!!
(defmacro H1+ () `(stack "H1")) ;; WWW DO NOT CONFUSE H1 with (1) !!!

;;; WWW H5 MUST be set using these functions!

(defmacro H5 () `(cell-symb (cell "H5")))
(defmacro H5+ () `(setf (H5) "+"))
(defmacro H5- () `(setf (H5) "-"))

(defmacro H3-cycles () `(cell-link (cell "H3")))

;;; This can trace strings, or any element (name/symb/link) of a cell
;;; incl. stackables.

(defvar *running?* nil)

;;; Example usage of *trace-@orID-exprs*
;;;   ("P051R050" (setf *trace-cell-names* '("W0" "W1" "H0" "H5") *cell-tracing-on* t))
;;;   ("P051R050" (setf *!!* '(:run :run-full :jdeep)))
;;; Can also be a number in which case it refers to the H3 value (@), as:
;;;   (123 ...)
;;; (setf *trace-@orID-exprs*
;;;    '(("P052R040"
;;;       (setf *trace-cell-names* '("W0" "W1" "H0") *cell-tracing-on* t)
;;;       (trace symbolify ipl-string-equal ipl-string-equal))
;;;      (123 (trace) (setf *cell-tracing-on* nil *!!* *default-!!list*))
;;;      ))

(defun trace-cells ()
  (let* ((cycle (h3-cycles))
	 (id (cell-id *trace-instruction*)))
    (mapcar #'eval
	    (loop for (key . exprs) in *trace-@orID-exprs*
		  if (or (and (numberp key) (= key cycle))
			 (and (stringp key) (string-equal key id)))
		  do (return exprs))))
  (when *cell-tracing-on*
    (loop for name in *trace-cell-names* do
	  (format t "   ~a=~s ++ ~s~%" name (cell name) (first-n 4 (gethash name *systacks*))))))

(defun store-cells (cells)
  (loop for cell in cells
	as name = (cell-name cell)
	unless (zero? name) ;; Until?
	do (store cell)))

;;; This is used for all IO at the moment, under the assumption (until otherwise
;;; demonstrated wrong) that LT does it's IO one line at a time, full processing
;;; those lines and then clearing the buffer and doing the next.

(defun blank80 () (subseq (format nil "~81d" 0) 0 80))
(defparameter blank80 (Blank80))
(defun blanks (n) (subseq blank80 0 n))
(defvar *W24-Line-Buffer* Blank80)

;;; ===================================================================
;;; Debugging Utils

;;; FFF Maybe make this a optional progn so that we don't have to put
;;; progns all over the place in order to trace. Args can be a fmt
;;; string and args, or a sequence of exprs that get eval'ed

(defvar *report-all-system-cells?* nil)

;;; This also checks to make sure that there isn't crap left on the
;;; stacks or in the cells and breaks if ther is. 

(defun report-system-cells (&optional (all? *report-all-system-cells?*))
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

(defun rems (target-sym) ;; report elements of memory with symbol
  (format t "Core:~%")
  (loop for cell-name being the hash-keys of *symtab*
	using (hash-value cell)
	as cell-symb = (and (cell? cell) (cell-symb cell))
	when (and (cell? cell)
		  (and (stringp cell-symb))
		  (string-equal target-sym cell-symb))
	do (format t "  ~s~%" cell))
  (format t "Stacks:~%")
  (loop for stack-name being the hash-keys of *systacks*
	using (hash-value cells)
	do (loop for cell in cells
		 as depth from 1 by 1
		 as cell-symb = (and (cell? cell) (cell-symb cell))
		 when (and (cell? cell)
			   (and (stringp cell-symb))
			   (string-equal target-sym cell-symb))
		 do (format t "  ~a(~a): ~s~%" stack-name depth cell))))


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
      (let ((missing-local-symbols (convert-local-symbols cells local-symbols.new-names)))
	(when (and missing-local-symbols (eq :code load-mode))
	  (setf cells (append cells (loop for missymb in missing-local-symbols
					  as new-name = (cdr (assoc missymb local-symbols.new-names :test #'string-equal))
					  do (!! :load "WARNING: Cell ~s being added for missing local symbol ~s!~%" new-name missymb)
					  collect (make-cell! :name new-name :pq "00" :symb "0" :link "0"))))))
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
		    (let ((new-symbol (newsym top-name)))
		      (setf (cell-name next-cell) new-symbol)
		      (setf (cell-link this-cell) new-symbol))
		    (setf (cell-link this-cell) next-name)))
	    (if (blank? this-symb)
		(if (blank? next-name)
		    (let ((new-symbol (newsym top-name)))
		      (setf (cell-name next-cell) new-symbol)
		      (setf (cell-symb this-cell) new-symbol))
		    (setf (cell-symb this-cell) next-name))))
      (store-cells cells)
      )))

;;; Convert-local-symbols goes trough all the instructions and changes
;;; the card-based representation of symbols like "9-100" to a
;;; generated one that has the name of the routine, like M123-9-100"
;;; (see warning about this coming back to bite use at the top of the
;;; module!) In addition, routines can use local symbols that are NOT
;;; defined in the routine. We need to add these to the routine, but
;;; that has to be done above this level, so in addition to the
;;; conversion process, we return the name of any symbol that has no
;;; local binding, and a cell gets created for each of these in the
;;; caller.

(defun convert-local-symbols (cells local-symbols.new-names &aux cell-names non-cell-names)
  (labels ((replace-symbols (cell accname.accessor)
	     (let* ((accessor (cdr accname.accessor))
		    (symbol (funcall accessor cell))
		    (new-name (cdr (assoc symbol local-symbols.new-names :test #'string-equal))))
	       (when new-name
		 (if (eq accessor #'cell-name)
		     (pushnew symbol cell-names :test #'string-equal)
		     (pushnew symbol non-cell-names :test #'string-equal))
		 (setf* (car accname.accessor) cell new-name)))))
    (loop for cell in cells
	  do
	  (loop for accname.accessor in *symbol-col-accessors*
		do (replace-symbols cell accname.accessor))))
  ;; Finally, return any symbols that are NOT in the found local symbols
  (set-difference non-cell-names cell-names :test #'string-equal))
			    
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

(defun prettify-jexps-if-any (cell)
  (when (cell? cell)
    (let* ((symbexp (getf (gethash (cell-symb cell) *jfn-plists*) 'explanation))
	   (linkexp (getf (gethash (cell-link cell) *jfn-plists*) 'explanation)))
      (if (or symbexp linkexp) (format nil "~%               [~a | ~a]" (or  symbexp "") (or linkexp ""))
	  ""))))

(defun reset! ()
  (clrhash *systacks*)
  (clrhash *symtab*) 
  (setup-j-fns)
  (clrhash *col->vals*)
  )

;;; The system cells are exactly like user-created cells. They have a
;;; specific name associated with a cell struct. What makes them
;;; special is just that they are "pushable" by creating cell-content
;;; stack entries that copy the contents of the named cell. The cell
;;; contents have no names and are not in the symtab; they exist only
;;; on the stack.

;;; (WWW S is not a cell just a symbol.)

(defparameter *system-cells* '("H0" "H1" "H3" "H5"))
(defparameter *w-cells* (loop for w below 43 collect (format nil "W~a" w)))
(defparameter *all-system-cells* (append *system-cells* *w-cells*))

(defun create-system-cells ()
  (loop for name in *all-system-cells*
	do
	(make-cell! :name name)
	(setf (gethash name *systacks*) (list :empty))
	(!! :dr-memory "Created system cell: ~s and its stack.~%" name))
  (setf (cell "S") "S-is-null")
  )

;;; If any var becomes nil, there's something wrong!  (:EMPTY is okay
;;; at the very end of the process.)

(defun check-for-overpopping ()
  (loop for name in *all-system-cells*
	as val = (gethash name *symtab*)
	if (null val)
	;; if (and (atom val) (or (eq :empty val) (null val)))
	do (break "**** Oops! ~s is ~s, which is oughtn't be!" name val)))

;;; This is needed because of H0 memory leaks, probably from JFNS.
(defvar *stack-depth-limit* 100)

(defun clean-stacks ()
  (check-for-overpopping)
  (when *stack-depth-limit*
    (loop for key being the hash-keys of *systacks*
	  using (hash-value stack)
	  as depth = (length stack)
	  do
	  (when (> depth *stack-depth-limit*)
	    (!! :dr-memory "Tailing stack ~a, now ~a deep, to ~a. [mem]~%" key depth *stack-depth-limit*)
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

(defvar *jfn->name* (make-hash-table :test #'equal))
(clrhash *jfn->name*) ;; In case we're reloading

(defmacro defj (name args explanation &rest forms)
  `(let ((uname ,(string-upcase (format nil "~a" name))))
     (setf (gethash uname *jfn-plists*) '(explanation ,explanation))
     (let ((fn (lambda ,args ,@forms)))
       (setf (gethash uname *symtab*) fn)
       (setf (gethash fn *jfn->name*) uname))))

;;; This is, alas, a bit heuristic because our strings can be
;;; addresses as well as simple strings. This results in a horrible
;;; screw case where LT uses individual characters, like left parens
;;; "(" for the address of working lists that are activated when a (
;;; is encountered (see card: "(000D000" (p. 181) ... Yes, that's
;;; really the id of the line: "(000D000" with a paren at the f'ing
;;; head!) One change I've made in order to help a bit with this
;;; confusion is that in LTFixed (and as flagged in the spreadsheet),
;;; I've changed the names of single-letter cells to be explicitly,
;;; so, for example: A becomes A0. 

(defun symbolify (arg jfn) ;; ?? FFF Might be able to use *fname-hint* here?
  (if (cell? arg) (cell-symb arg)
      (let* ((cell (<== arg)))
	(if cell (cell-symb cell)
	    (if (stringp arg) arg
	      (break "In ~a trying to interpret ~s as a string symbol." jfn arg))))))

(defvar *J991/2-emergency-hidey-hole* nil)

(defun setup-j-fns ()

  ;; THERE'S A TIMING PROBLEM WITH POPPING THE H0 STACK BEFORE CALLING
  ;; THE FUNCTION, WHICH IS THAT IF "H0" IS THE ARG, POPPING BEFORE THE
  ;; ACTION WILL GIVE YOU THE WRONG RESULT!!

  (defj J0 () "No operation")

  (defj J1 (arg0) "EXECUTE (0)"
    ;;; The process, (0), is removed from H0, H0 is restored (this
    ;;; positions the process's inputs correctly), and the process is
    ;;; executed as if its name occurred in the instruction in- stead
    ;;; of J1.
    (poph0 1) ;; Pre-popping in this case should be safe.
    (ipl-eval arg0))

  (defj J2 (arg0 arg1) "TEST (0) == (1)?" ;; The identity test
	;; is on the SYMBpart only; P and Q are ignored. [Also, in the
	;; case of alphabetics, trailing blanks or zeros are ignored.]
	;; Before we go anywhere else, the names could be equal or the
	;; name of one could be equal to the symbol of the other, in
	;; either direction. This is sooooooooo horrible!
	(!! :jdeep (announce "   ~a=~a" arg0 arg1))
	(if (ipl-string-equal arg0 arg1) (H5+) (H5-))
	(poph0 2)
	;; ("p.10: "...it is understood from the definition of TEST
	;; that J2 will remove both (0) and (1) from HO.")
	)

  (defj J3 () "SET H5 -" (H5-))
  (defj J4 () "SET H5 +" (H5+))
  (defj J5 () "REVERSE H5" (if (string-equal "+" (H5)) (H5-) (H5+)))

  (defj J6 () "REVERSE (0) and (1)" ;; USED IN F1
	(let ((r1 (cell-symb (H0)))
	      (r2 (cell-symb (first (H0+)))))
	  ;; !!! This is what you always have to do: Precompute your
	  ;; answers, then pop the inputs and push the outputs:
	  (poph0 2)
	  (ipush "H0" r1)
	  (ipush "H0" r2)))

  (defj J7 () "HALT, PROCEED ON GO"
    ;; The computer stops; if started again, it interprets the next
    ;; instruction in sequence. Aka....
    (break "J7: Processor halted ... use :C to continue."))

  (defj J8 () "RESTORE H0" (ipop "H0")) ;; USED IN ACKERMAN

  (defj J9 () "ERASE CELL (0)"
	;; Maybe remhash the name from the symtab? FFF
	(!! :jdeep "             .....J9 just pops H0; We don't need to do our own GC.~%")
	(poph0 1))

  (defj J10 (arg0 arg1) "FIND THE VALUE OF ATTRIBUTE (0) OF (1)" ;; USED IN LT
	;; If the symbol (0) is on the description list of list (1) as an
	;; attribute, then its value--i.e., the symbol following it--is output
	;; as (0) and H5 set + ; if not found, or if the description list
	;; doesn't exist, there is no output and H5 set - . (J10 is accomplished
	;; by a search and test of all attributes on the description list.) 
	(PopH0 2) ;; I think pre-popping is safe here because H0 won't ever be a list head.
	(!! :jdeep "             .....In J10 trying to find the value of ~s in ~s!~%" arg0 arg1)
	(!! :jdeep (announce "Find ~a in ~a" arg0 arg1))
	(let* ((list-head (cell arg1))
	       (dlist-name (cell-symb list-head))
	       (target arg0))
	  (!! :jdeep "             .....In J10 list-head = ~s, dlist-name = ~s, target = ~s~%" list-head dlist-name target)
	  (if (zero? dlist-name)
	      (progn (!! :jdeep "             .....In J10 -- no dl, so we're done with H5-~%") (H5-))
	      (loop with dl-attribute-cell = (cell (cell-link (cell dlist-name)))
		    do ;; Note we're skipping the dl of the dl if any
		    ;; The first could be the last. This is sort of messy. FFF Unduplicate code %%%
		    (if (null dl-attribute-cell)
			(progn (!! :jdeep "             .....J10 failed (a) to find ~s.~%" target) (H5-) (return nil)))
		    (!! :jdeep "             .....In J10 dl-attribute-cell = ~s~%" dl-attribute-cell)
		    (if (ipl-string-equal target (cell-symb dl-attribute-cell))
			(let* ((cell (cell (cell-link dl-attribute-cell))))
			  (!! :jdeep "             .....J10 found ~s at ~s, returning ~s~%" target dl-attribute-cell (cell-symb cell))
			  (H5+)
			  (ipush "H0" (cell-symb cell))
			  (return t))
			(let* ((next-att-link (cell-link dl-attribute-cell)))
			  (if (zero? next-att-link)
			      (progn
				(!! :jdeep "             .....J10 failed (b) to find ~s.~%" target)
				(H5-) (return nil))
			      (setf dl-attribute-cell (cell (cell-link dl-attribute-cell))))))))))

  (defj J11 (arg0 arg1 arg2) "ASSIGN (1) AS THE VALUE OF ATTRIBUTE (0) OF (2)"
	;; After J11, the symbol (1) is on the description list of
	;; list (2) as the value of attribute (0). If (0) was already
	;; on the description list, the old value has been removed,
	;; and (1) has taken its place; if the old value was local, it
	;; has been erased as a list structure (J72). If (0) is a new
	;; attribute, it is placed at the front of the description
	;; list. J11 will create the description list (with a local
	;; name) if it does not exist (head of (2) empty). There is no
	;; output in HO. *** Def. needs to pop late !!!
	(let* ((att arg0)
	       (val arg1)
	       (list-head (cell arg2))
	       (maybe-dl-head (cell-symb list-head))
	       (dl-head (if (not (zero? maybe-dl-head)) (cell maybe-dl-head)
			    (progn (!! :jdeep "             .....In J11 no dlist yet for ~s so I'm creating one!~%" list-head)
				   (make-cell! :name (newsym) :symb "0" :link "0"))))
	       )
	  ;; Either get the DL for the list, or create one if it doesn't exist.
	  ;; (This is redundant if it was already there)
	  (setf (cell-symb list-head) (cell-name dl-head))
	  (J11-helper-add-to-dlist dl-head att val)
	  (!! :jdeep (pll arg2))
	  (PopH0 3)
	  ))

  (defj J15 (arg0) "ERASE ALL ATTRIBUTES OF (0)"
	;; The description list of list (0) is erased as a list
	;; structure (J72), and the head of (0) is set empty.
	(let ((lhead (<== arg0)))
	  (!! :jdeep "             .....J15 clearing the dl of ~s (~s)~%" arg0 lhead)
	  (setf (cell-symb lhead) "0"))
	(poph0 1)
	)

  ;; ==================================================================
  ;; GENERATOR FUNCTIONALITY
  
  ;; Just as a reminder: (defvar *genstack* nil) (defstruct gentry fn wn :wnames +-)

  (defj J17 (wn-symb fn) "GENERATOR SETUP" 
	;; Has two inputs: (0) = Wn, the name of the highest W that will be
	;; used for working storage, e.g., (0) = W6, if cells WO through W6
	;; will be used. (1) = The name of the subprocess to be executed by
	;; generator. J17 does three things (and has no output):
	;; 1. Preserves the cells WO through Wn, thereby preserving the
	;; superroutine-subprocess context. 2. Stores Wn and the name of the
	;; subprocess in storage cells and preserves a third cell for the
	;; output sign of H5 (these three storage cells are called the
	;; generator hideout). 3. Obtains the trace mode of the
	;; superroutine, and records it in one of the hideout cells (see §
	;; 15.0, MONITOR SYSTEM).
	(poph0 2) ;; Safe -- never passed H0

	;; This is an ugly hack that grabs the previous generator processing fn, if 
	;; J18 is passed as the process function. ... At the moment it's been undone
	;; bcs instead I've made J18 actually remove the top entry from the genstack
	;; before IPL-EVAL re-entry, which has sort of the same effect, albeit cleaner.
	;; (!! :Jdeep "             J17 called with wn:~s and fn:~s~%" wn-symb fn)
	;; (when (string-equal fn "J18")
	;;   (setf fn (gentry-fn (car *genstack*)))
	;;   (!! :jdeep "             .....J18 HACK!! is replacing subFn with ~s~%" fn))

	(let* ((wn (parse-integer (subseq wn-symb 1 2))))
	  (J4n=preserve-wn wn)
	  (push (make-gentry :fn fn
			     :wn wn :wnames (first-n (1+ wn) *w-cells*)
			     ;; ??? There's an open issue of what
			     ;; happens if J19 is called before any of
			     ;; the cycles have executed. This could
			     ;; happen if the generating list or fn
			     ;; has no elements at all. My theory in
			     ;; this case is that the generator
			     ;; actually completed, although it
			     ;; completed running through a null list,
			     ;; so we return a +.
			     :+- "+")
		*genstack*))
	(!! :jdeep "             .....J17 *genstack* push: ~s~%" (car *genstack*)))

  (defj J18 () "EXECUTE SUBPROCESS" 
	;; Has no input. It does six things: 1. Restores the symbols
	;; in WO through Wn (generator context), thereby returning the
	;; previous context of symbols to the top of the W's
	;; (superroutine-subprocess context) 2. Stacks the generator
	;; context in a hideout cell. 3. Sets the trace mode of the
	;; subprocess to be that of the superroutine (see § 15.0,
	;; MONITOR SYSTEM). 4. Executes the subprocess. 5. Returns the
	;; symbols of the generator's context from the hideout to the
	;; W's, pushing the W's down, thereby preserving the
	;; superroutine-subprocess context. 6. Records H5, the
	;; communication of the sub-process to the generator (see
	;; J19), in one of the hideout cells.
	(let* ((gentry (first *genstack*))
	       (fn (gentry-fn gentry))
	       (wn (gentry-wn gentry))
	       (wnames (gentry-wnames gentry))
	       ;; WVALS is the generator context, held by the lisp
	       ;; stack. (So we don't need a special stack for the
	       ;; generator context.)
	       (wvals (loop for wname in wnames
			    as wcell = (cell wname)
			    do (ipop wname)
			    collect wcell)))
	  (!! :jdeep "             J18: *genstack* = ~s~%" *genstack*)
	  (!! :jdeep "             .....J18 (fn=~s, wn=~s)~%" fn wn)
	  ;; This seems redundant with the one in J19, but that one is
	  ;; restoring the caller context, whereas this one is
	  ;; restoring the generator context.
	  ;; (J3n=restore-wn wn) !!! This was causing double poppage ~ 20250415
	  ;; We also temporarily pull the top of the genstack to reveal what's underneath in case there is a recursive generator in use. 
	  (let ((held-genstack-entry (pop *genstack*)))
	    (!! :jdeep "             .....J18 holding ~s off the genstack...~%" held-genstack-entry)
	    (!! :jdeep "             .....*genstack* is now: ~s~%" *genstack*)
	    (!! :jdeep "             .....J18 Executing ~s~%" fn)
	    (ipl-eval fn)
	    (!! :jdeep "             .....J18 ~s returned with H5=~a~%" fn (H5))
	    ;; Now we put it back
	    (push held-genstack-entry *genstack*))
	  (loop for wname in wnames
		as wval in wvals
		do (ipush wname wval))
	  (setf (gentry-+- gentry) (H5))
	  ))

  (defj J19 () "GENERATOR CLEANUP"
	;; Has no input. Does three things: 1. Restores WO through
	;; Wn. 2. Restores all the cells of the hideout. 3. Places in
	;; H5. the recorded sign, which will be + if the generator went to
	;; completion (last subprocess communicated + ), and - if the
	;; generator was stopped (last subprocess communicated - ).
	(let* ((gentry (pop *genstack*))
	       (wn (gentry-wn gentry))
	       (+- (gentry-+- gentry)))
	  (!! :jdeep "             .....J19 popping gentry: ~s~%" gentry)
	  ;; This seems redundant with the one in J18, but that one is
	  ;; restoring the generator context, whereas this one is
	  ;; restoring the caller context.
	  (J3n=restore-wn wn) 
	  (if (string-equal +- "+") (H5+)
	      (if (string-equal +- "-") (H5-)
		  (break "In J19 +- is ~s" +-)))))

  ;; ==================================================================

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

  (defj J60 (arg0) "LOCATE NEXT SYMBOL AFTER CELL (0)" ;; USED IN F1
	;; LOCATE NEXT SYMBOL AFTER CELL (0). (0) is the name of a
	;; cell. If a next cell exists (LINK of (0) not a termination
	;; symbol), then the output (0) is the name of the next cell,
	;; and H5 is set +. If LINK is a termination symbol, then the
	;; output (0) is the input (0), which is the name of the last
	;; cell on the list, and H5 is set -. No test is made to see
	;; that (0) is not a data term, and J60 will attempt to
	;; interpret a data term as a standard IPL cell.  !!! Must pop
	;; late (if at all) !!!
	(let* ((this-cell (cell arg0))
	       (link (cell-link this-cell)))
	  (!! :jdeep "             .....In J60, this-cell = ~s, link = ~s~%" this-cell link)
	  (if (zero? link)
	      ;; Notice that we don't pop on eol!
	      (progn (!! :jdeep "             .....In J60 no next cell!~%") (H5-))
	      (progn (!! :jdeep "             .....In J60 next cell is ~s!~%" link)
		     (PopH0 1)
		     (H5+)
		     (ipush "H0" link)))))

  ;; WWW Many of these list operations are unclear on whether they are
  ;; matching/inserting the SYMB of the intended cell, for example
  ;; into a new cell, or the cell itself. In most cases it can't be
  ;; the cell itself because then linking it (or otherwise moving it
  ;; around) will unlike the cell from where it was, or otherwise mess
  ;; up the original cell, so I've taken these as usually creating new
  ;; cells, and testing for SYMB equivalence.

(defj J62 (arg0 arg1) "LOCATE (O) ON LIST (1)"
      ;; LOCATE (0) ON LIST (1). A search of list with name (1) is
      ;; made, testing each symbol against (0) (starting with cell
      ;; after cell (1)). If (0) is found, the output (0) is the
      ;; name of the cell containing it and H5 is set + . Hence, J62
      ;; locates the first occurrence of (0) if there are
      ;; several. If (0) is not found, the output (0) is the name of
      ;; the last cell on the list, and H5 set - . [This is a bit of
      ;; a problem, because the target could be a cell name or a
      ;; string, which is ambiguous if we're handed a string. We
      ;; heuristically see if the string can be a cell, in which
      ;; case we use that cell's symb. ... Is this complexity needed
      ;; anylonger with <== and <=!?]  Prob. actually safe to
      ;; pre-pop.
      (let* ((target arg0)
	     (list-head (cell arg1)))
	(!! :jdeep "             .....J62 trying to locate target:~s in linear list starting with cell ~s~%" target list-head)
	;; The H5 has to be set in the subfn bcs only it knows whether it succeeded.
	(let ((r (j62-helper-search-list-for-symb target list-head (cell-link list-head))))
	  (poph0 2) 
	  (ipush "H0" r))))

  (defj J63 (new-symbol list-cell-name) "INSERT (0) BEFORE SYMBOL IN (1)"
	;; (1) is assumed to name a cell in a list. A new cell is
	;; inserted in the list behind (1). The symbol in (1) is
	;; moved into the new cell, and (0) is put into (1). The end
	;; result is that (0) occurs in the list before the symbol
	;; that was originally in cell (1).
	(!! :jdeep "             .....******** In J64 WORRY ABOUT THE UNINTERPRETABLE TERMINATION CELL CASE!~%")
	(!! :jdeep "             .....=========================================================~%J64 trying to append ~s to ~s~%" new-symbol list-cell-name)
	(!! :jdeep "             .....Here are the lists before:~%")
	(let* ((list-cell (cell list-cell-name))
	       (new-cell-name (newsym))
	       (list-cell-symbol (cell-symb list-cell))
	       (new-cell (make-cell! :name new-cell-name :symb list-cell-symbol :link (cell-link list-cell))))
	  (setf (cell-symb list-cell) new-symbol
		(cell-link list-cell) new-cell-name))
	(!! :jdeep "             .....*********************************************************~%")
	(!! :jdeep "             .....Here is the target list, after:~%")
	(!! :jdeep (pl list-cell-name))
	(!! :jdeep "             .....=========================================================~%")
	(poph0 2)
	)

  (defj J64 (new-symbol list-cell-name) "INSERT (0) AFTER SYMBOL IN (1)"
	;; Identical with J63, except the symbol in (1) is left in
	;; (1), and (0) is put into the new cell, thus occurring after
	;; the symbol in (1). (If (1) is a private termination symbol,
	;; (0) is put in cell (1), which agrees with the definition of
	;; insert after.) [WWW???!!! I dunno WTF this is talking
	;; about! And it's prob. gonna break at list ends because
	;; ... see above!] 
	(!! :jdeep "             .....******** In J64 WORRY ABOUT THE UNINTERPRETABLE TERMINATION CELL CASE!~%")
	(!! :jdeep "             .....=========================================================~%J64 trying to append ~s to ~s~%" new-symbol list-cell-name)
	(!! :jdeep "             .....Here are the lists before:~%")
	(!! :jdeep (pl new-symbol) (pl list-cell-name))
	(let* ((list-cell (cell list-cell-name)))
	  (if (and (zero? (cell-symb list-cell)) (zero? (cell-link list-cell)))
	      (setf (cell-symb list-cell) new-symbol)
	      (setf (cell-link list-cell)
		    (cell-name (make-cell! :name (newsym)
					   :symb new-symbol
					   :link (cell-link list-cell))))))
	(!! :jdeep "             .....*********************************************************~%")
	(!! :jdeep "             .....Here is the target list, after:~%")
	(!! :jdeep (pl list-cell-name))
	(!! :jdeep "             .....=========================================================~%")
	(poph0 2)
	)

  ;; WWW If this tries to work with numeric data there's gonna be a
  ;; problem bcs PQ will be wrong.
  (defj J65 (arg0 arg1) "INSERT (0) AT END OF LIST (1)"
	(!! :jdeep (announce "~a =++ ~a" arg0 arg1))
	;; Identical to J66 except that it always inserts at the end
	;; of the list.
	(!! :jdeep "             .....=========================================================~%J65 trying to append ~s to ~s~%" arg0 arg1)
	(!! :jdeep "             .....Here are the lists before:~%")
	(!! :jdeep (pl arg0) (pl arg1))
	(loop with list-cell = (cell arg1)
	      with symb = arg0
	      with new-cell = (make-cell! :name (newsym) :symb symb :link "0")
	      do
	      (cond ((zero? (cell-link list-cell))
		     (!! :jdeep "             .....J65 hit end, adding ~s to the list at ~s!~%" new-cell list-cell)
		     (setf (cell-link list-cell) (cell-name new-cell))
		     (return t)))
	      ;; Move to next cell if nothing above returned out
	      (setf list-cell (cell (cell-link list-cell))))
	(!! :jdeep "             .....*********************************************************~%")
	(!! :jdeep "             .....Here is the target list, after:~%")
	(!! :jdeep (pl arg1))
	(!! :jdeep "             .....=========================================================~%")
	(PopH0 2)
	)
	

  (defj J66 (arg0 arg1) "INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT" ;; USED IN F1
	;; J66 INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT. A
	;; search of list (1) is made. against (0) (starting with the
	;; cell after cell (1) . If (0) is found, J66 does nothing
	;; further. If (0) is not found, it is inserted at the end of
	;; the list, as in J65. [Nb. This can't do anything sensible
	;; with a branching list!]
	(let ((target arg0))
	  (!! :jdeep "             .....J66 trying to insert ~s in ~s~%" target arg1)
	  (loop with list-cell = (<=! arg1)
		as link = (cell-link list-cell)
		do
		(cond ((string-equal (cell-symb list-cell) target)
		       (!! :jdeep "             .....J66 found ~s in the list already. No action!~%" target)
		       (PopH0 2) (return nil))
		      ((zero? link)
		       (!! :jdeep "             .....J66 hit end, adding ~s to the end of the list!~%" target)
		       (setf (cell-link list-cell)
			     (cell-name (make-cell! :name (newsym) :symb target :link "0")))
		       (PopH0 2) (return t)))
		;; Move to next cell if nothing above returned out
		(setf list-cell (cell (cell-link list-cell))))))
 
  (defj J68 (arg0) "DELETE SYMBOL IN CELL (0)"
	;; (0) names a cell in a list. The symbol in it is deleted by
	;; replacing it with the next symbol down the list (the next
	;; cell is removed from the list and returned to available
	;; space, so that the list is now one cell shorter). H5 is set
	;; + unless (0) is the last cell in the list or a termination
	;; cell. Then H5 is set - . Thus, H5- means that after J68,
	;; the input (0) (which is no longer in HO) is a termination
	;; cell (see discussion in § 9.4, DELETE). [This is weird! It
	;; moves the next symbol up and then deletes the NEXT
	;; cell....?]
	(let* ((this-cell (<== arg0)) ;; was <=!
	       (next-cell-name (cell-link this-cell)))
	  (if (zero? next-cell-name)
	      (progn (!! "J68 hit the end of the list.~%")
		     (H5-))
	      ;; Here's the complex work. Ugh!
	      (let* ((next-cell (cell next-cell-name)))
		(!! "J68 Moving symbol in ~s to ~s and deleting ~s.~%"
		    next-cell this-cell next-cell)
		(setf (cell-symb this-cell) (cell-symb next-cell)
		      (cell-link this-cell) (cell-link next-cell)))))
	(poph0 1)
	)

  (defj J71 (arg0) "ERASE LIST (0)"
	(declare (ignore arg0))
	;; (0) is assumed to name a list. All cells of the list--both
	;; head and list cells--are returned to available
	;; space. (Nothing else is returned, not even the description
	;; list of (0), if it exists.) There is no out-put in HO. If
	;; (0) names a list cell, the cell linking to it will be
	;; linking to available space after J71, a dangerous but not
	;; always fatal situation.
	(poph0 1))

  (defj J72 (arg0) "ERASE LIST STRUCTURE (0)"
	(declare (ignore arg0))
	;; (0) is assumed to name a list structure or a sublist
	;; structure. List (0) is erased, as are all lists with local
	;; names on list (0), and all lists with local names on them,
	;; and so on. Thus, description lists get erased, if they have
	;; local names. If the list is on auxiliary storage (Q of (0)
	;; = 6 or 7), then the list structure is erased from
	;; auxiliary, and the head, (0), is also erased. [Mostly this
	;; is a noop since we use lisp GC and aren't really worried
	;; about memory. Some day FFF this should remhash the cells in
	;; the list from the symtab.]
	(PopH0 1))

  (defj J73 (arg0) "Copy list"
	;; COPYLIST (0). The output (0) names a new list, with the identical
	;; symbols in the cells as are in the corresponding cells of list (0),
	;; including the head. If (0) is the name of a list cell, rather that
	;; [sic: than] a head, the output (0) will be a copy of the remainder of
	;; the list from (0) on. (Nothing else is copied, not even the
	;; description list of (0), if it exists.)  The name is local if the
	;; input (0) is local; otherwise, it is internal.
	(let* ((r (cell-name (copy-ipl-list-and-return-head arg0))))
	  (poph0 1)
	  (ipush "H0" r)))

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
	(!! :jdeep "             .....J74 is copying list: ~s~%" (H0))
	(let* ((r (copy-list-structure arg0)))
	  (poph0 1)
	  (ipush "H0" r)))

  (defj J75 (arg0) "DIVIDE LIST AFTER LOCATION (0)"
	;; (0) is assumed to be the name of a cell on a list. A
	;; termination symbol is put for LINK of (0), thus making (0)
	;; the last cell on the list. The output (0) names the
	;; remainder list: a new blank head followed by the string of
	;; list cells that occurred after cell (0).
	(let* ((split-cell (<== arg0))
	       (new-head (make-cell! :name (newsym) :link (cell-link split-cell))))
	  (setf (cell-link split-cell) "0")
	  (!! :jdeep "             .....J75 splitting a list: New tail: ~s, New head (H0): ~s~%" split-cell new-head)
	  (let* ((r (cell-name new-head)))
	    (poph0 1)
	    (ipush "H0" r))))

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
	(let* ((l0 (<=! arg0))
	       (c1 (<=! arg1))
	       (c1link (cell-link c1))
	       (last-cell-in-l0 (last-cell-of-linear-list l0)))
	  (cond ((zero? (cell-link l0))
		 (poph0 2)
		 (ipush "H0" c1)
		 (H5-))
		(t (setf (cell-link c1) (cell-link l0))
		   (setf (cell-link last-cell-in-l0) c1link)
		   (poph0 2)
		   (ipush "H0" last-cell-in-l0)))))

  (defj J78 (arg0) "TEST IF LIST (0) IS NOT EMPTY"
	;; H5 is set - if LINK of (0) is a termination symbol, and set + if not.
	(if (zero? (cell-link (cell arg0))) (H5-) (H5+))
	(poph0 1)
	)

  (defj J79 (arg0) "TEST IF CELL (0) IS NOTEMPTY"
	;; H5 is set - if SYMB of (0) is 0, and set + otherwise. (Q of
	;; (0) is ignored; thus, both cells holding internal zero and
	;; termination cells give H5-). [??? It looks like this should
	;; be getting the name of a cell, but in the one call that
	;; it's used in LT - M054R130 - H0={...|0|0|0}, so ...hmmmm?]
	(if (zero? arg0) (format t "WARNING: @~a J79 IS PROBABLY GETTING BAD INPUT: ~s~%" (h3-cycles) arg0))
	(if (or (zero? arg0) (zero? (cell-symb (cell arg0)))) (H5-) (H5+))
	(poph0 1))

  ;; J8n: FIND THE nth SYMBOL ON LIST (0) 0 <== n <== 9. (Ten routines: J80-J89)
  ;; Set H5 + if the nth symbol exists, - if not. Assume list (0) describable,
  ;; so that J81 finds symbol in first list cell, etc. J80 finds symbol in head;
  ;; and sets H5- if (0) is a termination symbol. 

  (defj J80 (arg0) "FIND THE HEAD SYMBOL OF (0)"
	(h5+)
	(if (zero? arg0)
	    (H5-)
	    (let* ((r (cell-symb (cell arg0))))
	      (poph0 1)
	      (ipush "H0" r))))

;;; FIND THE NTH SYMBOL ON LIST (0) Ten routines, J80-J89. Set H5+ if
;;; the Nth symbol exists, - if not. Assume list (0) is de-scribable,
;;; so that J81 finds symbol in first list cell, etc. J80 finds
;;; symbol in head; and sets H5- if (0) is a termination symbol.

  (defj J81 (arg0) "FIND THE 1st (non-head) SYMBOL OF (0)"
	(j8n-helper (cell-link (cell arg0)) 1))

  (defj J82 (arg0) "FIND THE 2nd (non-head0 SYMBOL OF (0)"
	(j8n-helper (cell-link (cell arg0)) 2))
	      
  ;; J9n CREATE A LIST OF THE n SYMBOLS (n-1), (n-2), ..., (1), (0), 0
  ;; < n < 9. The order is (n-1) first, (n-2) second, ..., (0)
  ;; last. The output (0) is the name (internal) of the new list; it
  ;; is describable. J90 creates an empty list (also used to create
  ;; empty storage cells, and empty data terms).

  (defj J90 () "Create a blank cell on H0"  ;; USED IN F1
	;; J90: Get a cell from the available space list, H2, and leave its name in HO.
	;; J90 creates an empty list (also used to create empty storage cells, and empty data terms).
	;; The output (0) is the name a the new list.
	(let* ((name (newsym))
	       (cell (make-cell! :name name :pq "00" :symb "0" :link "0")))
	  (!! :jdeep "            .....J90 creating blank list cell: ~s~%" cell)
	  (ipush "H0" name)))

  (defj J91 () "Create a list of 1 entry" (J9n-helper 1))
  (defj J92 () "Create a list of 2 entries" (J9n-helper 2))
  (defj J93 () "Create a list of 3 entries" (J9n-helper 3))

  (defj J100 (arg0 arg1) "GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0)" ;; USED IN LT
	;; J100 GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0). The subprocess
	;; named (0) is performed successively with each of the symbols of list named
	;; (1) as input. The order is the order on the list, starting with the first
	;; list cell. H5 is always set + at the start of the subprocess. J100 will
	;; move in list (1) if it is on auxiliary. [This assumes a linear list.]
	(!! :jdeep "             .....J100 GENERATE SYMBOLS FROM LIST ~s FOR SUBPROCESS ~s~%" arg1 arg0)
	(loop with cell-name = (cell-link (cell arg1))
	      with cell = nil
	      with exec-symb = arg0
	      with inputs-popped = nil
	      until (zero? cell-name)
	      do 
	      (!! :jdeep "             .....J100: cell-name=~s, cell=~s~%" cell-name cell)
	      (setf cell (cell cell-name))
	      ;; Setup: arg->H0 and H5=+
	      (let* ((r (cell-symb cell)))
		;; This only pops the 2 inputs on the first call-down! Be afraid...be very afraid!
		(unless inputs-popped (poph0 2) (setf inputs-popped t))
		(ipush "H0" r))
	      (H5+)
	      (!! :jdeep "             .....J100: Exec'ing ~s on ~s~%" exec-symb (cell-symb (h0)))
	      (ipl-eval exec-symb)
	      (setf cell-name (cell-link cell))
	      (!! :jdeep "             .....J100 returned, H5=~s, next cell-name=~s~%" (H5) cell-name)
	      ))

  (defj J110 (arg0 arg1 arg2) "(1) + (2) = (O)" 
	;; The number (0) is set equal to the algebraic difference between numbers
	;; (1) and (2). The output (0) is the input (0). (The popping here is complex!)
	(let* ((n1 (numget arg1))
	       (n2 (numget arg2))
	       (r (+ n1 n2)))
	  (!! :jdeep "             .....J110: ~a + ~a = ~a~%" n1 n2 r)
	  (poph0 -2) ;; This pops 2 items of the H0 stack UNDER the top. (Top unchanged!)
	  (numset arg0 r)))

  (defj J111 (arg0 arg1 arg2) "(1) - (2) -> (O)." ;; USED IN ACKERMAN
	;; The number (0) is set equal to the algebraic difference between numbers
	;; (1) and (2). The output (0) is the input (0). (The popping here is complex!)
	(let* ((n1 (numget arg1))
	       (n2 (numget arg2))
	       (r (- n1 n2)))
	  (!! :jdeep "             .....J111: ~a - ~a = ~a~%" n1 n2 r)
	  (poph0 -2) ;; This pops 2 items of the H0 stack UNDER the top. (Top unchanged!)
	  (numset arg0 r)))

  (defj J114 ([0] [1]) "TEST IF (0) = (1)" 
	(if (= (numget [0]) (numget [1])) (h5+) (h5-))
	(poph0 2))

  (defj J115 ([0] [1]) "TEST IF (0) > (1)" 
	(if (> (numget [0]) (numget [1])) (h5+) (h5-))
	(poph0 2))

  (defj J116 ([0] [1]) "TEST IF (0) < (1)"
	(if (< (numget [0]) (numget [1])) (h5+) (h5-))
	(poph0 2))

  (defj J117 (arg0) "TEST IF (0) = 0." ;; USED IN ACKERMAN
	(let* ((n (numget arg0)))
	  (!! :jdeep "             .....J117: Testing if ~s (~s: ~s) = 0?~%" arg0 (<=! arg0) n)
	  (if (zerop n) (H5+) (H5-)))
	(poph0 1))

  (defj J120 (arg0) "COPY (0)"
	;; COPY (0). The output (0) names a new cell containing the
	;; identical contents to (0). The name is local if the input
	;; (0) is local; otherwise, it is internal.
	;; (No pop bcs H0 is replaced -- Maybe pop and push?)
	(let ((old-cell (cell arg0)))
	  (setf (h0) ;; This is probably redundant since the make-cell! set it in the symtab
		(make-cell!
		 :name "H0"
		 :symb (cell-name 
			(make-cell! :name (newsym)
				    :pq (cell-pq old-cell)
				    :symb (cell-symb old-cell)
				    :link (cell-link old-cell)))))))
  
  (defj J121 (to from) "SET (O) IDENTICAL TO (1)"
	;; The contents of the cell named (1) is places in the cell
	;; (0). The output (0) is the input (0). [????]
	(setf (cell-link (cell to)) (cell-link (cell from)))
	(poph0 2)
	(ipush "H0" to))

  (defj J124 (arg0) "CLEAR (0)" ;; USED IN LT
	;; The number (0) is set to be 0. If the cell is not a data
	;; term, it is made an integer data term=0. If a number, its
	;; type, integer, or floating point, is unaffected. It is left
	;; as the output (0).  (NO POP!?!?)
	(!! :jdeep "             .....J124: Clear (H0): ~s~%" arg0)
	(numset arg0 0))

;************************************* 

  (defj J125 (arg0) "TALLY 1 IN (0)" ;; USED IN ACKERMAN
	;; An integer 1 is added to the number (0). The type of the result
	;; is the same as the type of (0). It is left as the output
	;; (0). [NNN: If there is no value in (0) this assumes zero and
	;; set the number to 1"
	;; NO POP! "It is left as the output (0)." !!
	(let* ((curval (numget arg0)))
	  (!! :jdeep "             .....J125: Tally (0) currently: ~s~%" arg0)
	  (numset arg0
		  (if (not (numberp curval))
		      (progn (!! :jdeep "             .....Warning! J125 was sent a non-number: ~s, setting result to 1~%" curval) 1)
		      (1+ curval)))))

  (defj J126 (arg0) "COUNT LIST (0)"
	;; The output (0) is an integer data term, whose value is the
	;; number of list cells in list (0) (i.e., it doesn't count
	;; the head). If (0) = H2, J126 will count the available space
	;; list. This is the only place where H2 can be used safely by
	;; the programmer. [Nb. H2 is not passed to COUNT LIST in LT]
	(let* ((count-cell (make-cell! :name (newsym) :pq "12" :link 0))
	       (count-cell-name (cell-name count-cell))
	       (list-head (cell arg0))
	       (next-cell-name (cell-link list-head))
	       (count 0))
	  (!! :jdeep "             J126 counting ~a:~%" arg0)
	  (!! :jdeep (pll (cell arg0)))
	  (loop until (zero? next-cell-name)
		do (incf count)
		(setf next-cell-name (cell-link (cell next-cell-name)))
		finally (progn (poph0 1)
			       (numset count-cell-name count)
			       (!! :jdeep "             J126 result is ~s:~%" count-cell)
			       (ipush "H0" count-cell-name))
		)))

  (defj J130 (arg0) "TEST IF (O) IS REGIONAL SYMBOL"
	;; Tests if Q = 0 in arg0. [WWW ??? We might want this to
	;; actually do something a little more un-IPL-ish, like look
	;; at the symbol and make sure it starts with a letter.]
	(if 
	 (regional-symbol? arg0)
	 (H5+) (H5-))
	(poph0 1))

  (defj J133 (l) "TEST IF LIST (0) HAS BEEN MARKED PROCESSED"
	;; Tests if P = 1 (and Q != 1 or 5) in the cell whose name is
	;; (0). It will only be 1 if list (0) has been preserved and P
	;; = 1 put in its head by J137. This means list (0) has been
	;; marked processed. 
	(poph0 1)
	(let* ((l (<== l))
	       (pq (cell-pq l))
	       (q (getpq :q pq))
	       (p (getpq :p pq)))
	  (if (and (= p 1) (member q '(0 2 3 4 6 7)))
	      (H5+) (H5-))))

  (defj J136 (H0) "MAKE SYMBOL (O) LOCAL."
	;; The output (0) is the input (0) with Q = 2. Since all
	;; copies of this symbol carry along the Q value, if a symbol
	;; is made local when created, it will be local in all its
	;; occurrences. [I have no idea what his last sentence means!]
	;; (No pop bcs output is the input)
	(let ((cell (<== H0)))
	  (setf (cell-pq cell)
		(let* ((pq (cell-pq cell))
		      (l (length pq)))
		  (case l
		    (0 "02")
		    (1 (!! :jdeep "             !!!!!Warning: J136 assuming ~s is q-only!~%" H0) "02")
		    (2 (setf (aref pq 1) #\2) pq)
		    (t (Error "In J136 got ~s for pq in ~s" pq cell)))))))

  ;; This is deeply upsetting -- it pushes a non-system element -- the
  ;; head of a list, meaning that any named cell can be pushed and
  ;; restored. I think that ipush and ipop will do the thing, but
  ;; ... who knows!

  (defj J137 (l) "MARK LIST (0) PROCESSED"
	;; List (0) is preserved [ipushed], its [new] head made empty (Q =
	;; 4, SYMB = 0), and P set to be 1. Restoring (0) will return
	;; (0) to its initial state. This will work even with data
	;; terms. The output (0) is the input (0).
	(poph0 1)
	(ipush l) ;; This will leave a copy in the main symtab.
	(let ((newmain (cell l))) ;; This should be the NEW copy of the pushed head.
	  ;; Now we mark the new main cell as indicated.
	  (setf (cell-pq newmain) "14" (cell-symb newmain) "0")
	  ))

  (defj J138 (arg0) "J138 MAKE SYMBOL (O) INTERNAL"
	;; The output (0) is the input (0) with Q = 4. Best considered
	;; as "unmake local symbol." [Whatever the f any of that
	;; means! This is one of those confusing ones where it seems
	;; to indicate that the symbol includes the PQ.]
	(setf (cell-pq (H0)) (format "~a4" (aref (cell-pq (H0)) 0))))

  (defj J147 (arg0) "MARK ROUTINE (O) TO TRACE"
	;; FFF Maybe actually turn tracing on! :-)
	(poph0 1))

  (defj J148 () "MARK ROUTINE (0) TO PROPAGATE TRACE." 	;; Pop????
	;; Identical to J147, except uses Q = 4.
	(!! :jdeep "             .....J148 (MARK ROUTINE (0) TO PROPAGATE TRACE.) is a noop."))

  ;; Input and output are completely kludged, and unlike in original IPL. Partly
  ;; this is required because we don't have the same sort of physical
  ;; environment. There are tapes, and so on. But also, partly it's for
  ;; kludge-convenience. For example, there is exactly one 80 column
  ;; input/output buffer and it's used for all input and output.

  (defj J151 (arg0) "Print list (0)" ;; USED IN F1
	(print-linear-list (cell arg0))
	(PopH0 1)
	)

  (defj J152 (arg0) "PRINT SYMBOL (0)" ;; USED IN ACKERMAN
	;; Pop after!!
	(PopH0 1)
	(pretty-print-cell (cell arg0)))

  (defj J154 () "Clear print line"
	;; Clear Print Line CLEAR PRINT LINE. Print line 1W24 is cleared and the
	;; current entry column, 1W25, is set equal to the left margin, 1W21 [always 1 at the moment].
	(setf *W24-Line-Buffer* (blank80))
	(W25-set 0))

  (defj J155 () "Print line"
	(format t "~a~%" *W24-Line-Buffer*)
	)

  (defj J156 (arg0) "ENTER SYMBOL (0) LEFT-JUSTIFIED"
	;; Symbol (0) is entered in the current print line with its
	;; leftmost character in print position 1W25, 1W25 is advanced
	;; to the next column after those in which (0) is entered, and
	;; H5 is set + . If (0) exceeds the remaining space, no entry
	;; is made and H5 is set - .
	(PopH0 1)
	(let* ((s (cell-symb (<=! arg0)))
	       (l (length s))
	       (p (W25-get)))
	  (!! :jdeep "             .....J156 trying to add ~s at pos ~a in print butter.~%" s p)
	  (if (<= (+ p l) 80)
	      (loop for m from p by 1
		    as c across s
		    do (setf (aref *W24-Line-Buffer* m) c)
		    finally (progn (W25-set (+ l p))
				   (H5+)))
	      (H5-)))
	(!! :jdeep "             .....Print buffer is now:~%~s~%" *W24-Line-Buffer*)
	)

  (defj J157 (a0) "ENTER DATA TERM (0) LEFT-JUSTIFIED"
	;; Data term (0) is entered in the current print line with its
	;; leftmost character in print position 1W25, 1W25 is
	;; advanced, and H5 is set + . If (0) exceeds the remaining
	;; space, no entry is made and H5 is set - .
	(poph0 1)
	(block J157A
	  (let* ((s (cell-symb (cell a0)))
		 (l (length s))
		 (p (W25-get)))
	    (!! :jdeep "             .....J157 called on ~s, string: ~s (w25=~a)~%" a0 s p)
	    (when (> (+ l p) 80) (H5-) (return-from J157A nil)) ;; (Sadly, J157 isn't a DEFUN'ed block)
	    (loop for c across s
		  as i from p by 1
		  do (setf (aref *W24-Line-Buffer* i) c))
	    (W25-set (+ l p))
	    (H5+)
	    (!! :jdeep "             .....Print buffer is now:~%~s (w25=~a)~%" *W24-Line-Buffer* (+ l p))
	    )))

  (defj J160 (col) "TAB TO COL (0)"
	(poph0 1)
	(W25-set (numget col)))

  (defj J161 (a0) "INCREMENT COLUMN BY (0)"
	;; (0) is taken as the name of an integer data term. Current
	;; entry column, 1W25, is set equal to 1W25 + (0).
	(poph0 1)
	(W25-set (+ (cell-link (cell a0)) (W25-get))))
  
  (defj J166 () "SAVE ON UNIT (O) FOR RESTART"
	(PopH0 0)
	(!! :jdeep "             .....Yeah, I'm gonna pass on implementing J166 (Save for restart)!~%")
	)

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
	  (H5+)
	  (if line (scan-input-into-*W24-Line-Buffer* line) (H5-))
	  (W25-set 0)
	  ))
	
  (defj J181 () "INPUT LINE SYMBOL." ;; USED IN LT
	;; INPUT LINE SYMBOL. The IPL symbol in the field starting in column
	;; 1W25, of size 1W30, in line 1W24, is input to HO and H5 is set +. The
	;; symbol is regional if the first (leftmost) column holds a regional
	;; character; otherwise, it is absolute internal. All non-numerical
	;; characters except in the first column are ignored. If the field is
	;; entirely blank, or ignored, there is no input to HO, and H5 is set
	;; -. In either case, 1W25 is incremented by the amount 1W30. (J181
	;; turns unused regional symbols into empty but used symbols.)
	(let* ((w25p (w25-get))
	       (w30n (numget (cell-symb (cell "W30"))))
	       (start (1- w25p))
	       (end (+ start w30n))
	       (string (subseq *W24-Line-Buffer* start end)))
	  ;; Note that, unlike J182, here "All non-numerical
	  ;; characters except in the first column are ignored." So we
	  ;; need a special scraping step to carry this out.
	  (setf string (j181-helper-remove-non-numeric-except-first string))
	  (!! :jdeep "             .....J181 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a]~%" string start end *W24-Line-Buffer* w25p w30n)
	  (W25-set (+ (W25-get) w30n))
	  (if (regional-symbol? string)
	      (progn
		(!! :jdeep "             .....J181 decided that ~s IS a regional symbol, so we're installing it.~%" string)
		(make-cell! :name string :symb "0" :link "0")
		(ipush "H0" string)
		(H5+))
	      (progn
		(!! :jdeep "             .....J181 decided that ~s is NOT a regional symbol.~%" string)
		(ipush "H0" string)
		(H5-)))))

  (defj J182 (arg0) "INPUT LINE DATATERM (0)" ;; USED IN LT
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
	(let* ((w25p (W25-get))
	       (w30n (numget (cell-symb (cell "W30"))))
	       (start w25p)
	       (end (+ start w30n))
	       (string (subseq *W24-Line-Buffer* start end)))
	  ;; WWW Assumes that the target is alpha, which could be wrong in future applications!
	  (setf (cell-symb (cell arg0)) string) 
	  (W25-set (+ (W25-get) w30n))
	  (!! :jdeep "             .....J182 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a] and jammed it into ~s~%"
	      string start end *W24-Line-Buffer* w25p w30n arg0)
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
  ;; scanned-for character.) [Nb. W25 is NOT changed!]

  (defj J183 (arg0) "SET (0) TO NEXT BLANK"
	;; 183/4 the term indicated by (0) is updated, so NO POP H0!
	(J183/4-Scanner arg0 :blank))
 
  (defj J184 (arg0) "SET (0) TO NEXT NON-BLANK"
	;; Same as J183, except scans for any non-blank character.
	;; 183/4 the term indicated by (0) is updated, so NO POP H0!
	(J183/4-Scanner arg0 :non-blank))

  (defj J186 () "INPUT LINE CHARACTER"
	;; The character in column 1W25 of line 1W24 is input to HO,
	;; H5 is set +. If the character is numerical, that internal
	;; symbol is input; if the character is non-numerical, the
	;; zeroth symbol in the region designated by that character is
	;; input; i.e., A->AO, 3->3. If the character is a blank,
	;; there is no input and H5 is set - In either case, 1W25 is
	;; not advanced.
	(let* ((c (aref *W24-Line-Buffer* (1- (w25-get)))))
	  (!! :jdeep "             .....J186 read ~s~%" c)
	  (if (char-equal #\space c)
	      (H5-)
	      (progn
		(ipush "H0" (format nil (if (numchar? c) "~c" "~c0") c))
		(H5+)))))

  (defj J14 () "Unimplemented!" (break "J14 is unimplemented!")) ;; ERASE ATTRIBUTE(0) OF (1) **

  (defj J991 () "EMERGENCY HIDE"
	(setf *J991/2-emergency-hidey-hole*
	      (list (cell-symb (cell "H0"))
		    (cell-symb (cell "W1")))))
  
  (defj J992 () "EMERGENCY RECORVER"
	(ipush "H0" (first *J991/2-emergency-hidey-hole*))
	;(ipush "W1" (second *J991/2-emergency-hidey-hole*))
	)

  )


;;; ===================================================================
;;; JFn Utilities

;;; Used to pop the inputs of JFns. You need to be VERY CAREFUL about
;;; when in the JFn you do pop the args bcs the JFn may want to use
;;; H0! If n is negative, it pops the top of the underlying stack w/o
;;; replacing the main (some JFns need this to happen).

(defun PopH0 (n) (dotimes (i (abs n)) (if (< n 0) (pop (H0+)) (ipop "H0"))))

(defparameter *LT-Regional-Chars* "ABCDEFGIKLMNOPQRSTUVXYZ-*=,/+.()'")

;;; This version of equal understands various special features of
;;; strings and numbers that are specific to IPL-V, esp. that right
;;; blanks (and zeros!) are irrelevant in string equality. (Per Manual
;;; pg. 215)

(defun ipl-string-equal (a b)
  (string-equal (right-string-trim "0 " a) (right-string-trim "0 " b)))

(defun right-string-trim (cs s)
  (subseq s 0 (loop for p from (1- (length s)) downto 0
		    until (not (find (aref s p) cs :test #'char-equal))
		    finally (return (1+ p)))))

(defun J9n-helper (n)
  (let* ((head-name (newsym)) ;; Needed for tracing later
	 (head (make-cell! :name head-name :pq "00" :symb "0" :link "0"))
	 ;; The order is (n-1) first, (n-2) second, ... (0) last.
	 (symbols `(,@(reverse (loop for hn in (H0+) as m below n collect (cell-symb hn))) ,(cell-symb (h0))))
	 )
    (loop for sym in symbols
	  with prev-cell = head
	  as next-cell-name = (newsym)
	  as next-cell = (make-cell! :name next-cell-name :pq "00" :symb sym :link "0")
	  do 
	  (setf (cell-link prev-cell) next-cell-name)
	  (setf prev-cell next-cell))
    (poph0 n)
    (ipush "H0" head-name)
    (!! :jdeep "            .....J9n created list: ~%")
    (!! :jdeep (pl head-name))))

(defun J11-helper-add-to-dlist (dlist-head att val &key (if-aleady-exists :replace)) ;; :error :allow-multiple
  (!! :jdeep "             .....ADD-TO-DLIST entry: dlisthead = ~s, att=~s, val=~s~%" dlist-head att val)
  (loop with next-att-cell = (cell-link dlist-head)
	with last-val-cell = dlist-head ;; In case we fall through immediately
	with next-val-cell = nil	;; gets set below
	until (zero? next-att-cell)
	do
	(setf next-att-cell (cell next-att-cell)) ;; Can't do this above bcs need zero? check
	(setf next-val-cell (cell (cell-link next-att-cell)))
	(!! :jdeep "             .....ADD-TO-DLIST is checking next-att-cell=~s, last-val-cell=~s~%" next-att-cell last-val-cell)
	(if (ipl-string-equal att (cell-symb next-att-cell))
	    (case if-aleady-exists
	      (:replace
	       (!! :jdeep "             .....In J11 (helper) replacing ~s symbol with ~s~%" next-val-cell val)
	       (setf (cell-symb next-val-cell) val) (H5+) (return t))
	      (:error (error "In ADD-TO-DLIST, att ~a already exits in ~s" att dlist-head))
	      (:allow-multiple nil) ;; When we get to the end we'll add a new one.
	      ))
	;; Move forward
	(setf last-val-cell next-val-cell
	      next-att-cell (cell-link last-val-cell))
	finally
	;; If we got here we're holding the last val in last-val-cell
	;; and need to append the new att and val. The one edge case is
	;; if there are not atts at all, in which case last-val-cell
	;; will be dlist-head ... which I hope is right!
	(let*
	    ((new-val-cell (make-cell! :name (newsym) :symb val :link "0"))
	     (new-att-cell (make-cell! :name (newsym) :symb att :link (cell-name new-val-cell))))
	  (!! :jdeep "             .....ADD-TO-DLIST taking the finally option: last-val-cell=~s, new-att-cell = ~s, new-val-cell=~s~%"
	      last-val-cell new-att-cell new-val-cell)
	  (setf (cell-link last-val-cell) (cell-name new-att-cell))
	  (H5+)
	  (return t))))

(defun dlist-of (listhead &key (create-if-does-not-exist? nil))
  (let* ((dlisthead (cell-symb listhead)))
    (if (not (zero? dlisthead)) (cell dlisthead)
	(if (not create-if-does-not-exist?)
	    (error "DLIST-OF wants there to already be a dlist in ~s" listhead)
	    (let* ((dlname  (newsym (cell-name listhead)))
		   (dlhead (make-cell! :name dlname :symb "0" :link "0")))
	      (setf (cell-symb listhead) dlname)
	      dlhead)))))
	      
;;; Assumes a linear list.

(defun j8n-helper (cell-name nth)
  (cond ((zero? cell-name)
	 (poph0 1)
	 (H5-))
        ((= nth 1) (H5+)
	 (let* ((r (cell-symb (cell cell-name))))
	   (poph0 1)
	   (ipush "H0" r)))
	(t (j8n-helper (cell-link (cell cell-name)) (1- nth)))))

(defun j62-helper-search-list-for-symb (target incell inlink)
  (cond ((zero? inlink)
	 (H5-)
	 incell)
	((ipl-string-equal (cell-symb incell) target)
	 (H5+)
	 incell)
	(t (j62-helper-search-list-for-symb target (cell inlink) (cell-link incell)))
	))

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

(defun regional-symbol? (string)
  (and (find (aref string 0) *LT-Regional-Chars*)
       (loop for p from 1 by 1
	     with lim = (1- (length string))
	     until (= p lim)
	     if (not (find (aref string p) "0123456789"))
	     do (return nil)
	     finally (return t))))

(defun w25-get () (numget (cell-symb (cell "W25"))))
(defun w25-set (n) (numset (cell-symb (cell "W25")) n))
(defun w25-init ()
  (make-cell! :name "W25"
	      :symb (cell-name (make-cell! :name (newsym "W25") :pq "12" :link 1))))

;;; These number things have to be given the name of what is supposed
;;; to be a numerical data cell, that is, one where the link is
;;; expected to be a number.

(defun numget (sym)
  (let* ((data-cell (cell sym))
	 (n (cell-link data-cell)))
    (if (not (numberp n))
	(break "Numget was asked to get a non-number ~s from ~s (~s)." n data-cell sym)
	(if (>= n 0) n (break "Numget was asked to get a negative number ~a from  ~s (~s)." n data-cell sym)))))

(defun numset (sym n)
  (let* ((data-cell (cell sym)))
    (unless (numberp (cell-link data-cell))
      (!! :deep-alerts
	  "WARNING: NUMSET was asked to set ~s (via ~s) which doesn't already have a number in the link.~%"
	  data-cell sym))
    (setf (cell-link data-cell) n)))

;;; !!! WWW OBIWAN UNIVERSE WITH LISP ZERO ORIGIN INDEXING WWW !!!
;;; (NNN H0p might be deprecated FFF Remove?)

(defun J183/4-Scanner (arg0 mode)
  ;; NO POP H0! ("...leave (0)")
  (let* ((counter arg0)
	 (w25p (W25-get)))
    (!! :jdeep "             .....Starting in J183/4-Scanner: counter = ~s, w25p = ~a~%" counter w25p)
    (if (not (numberp w25p)) (break "In J183/4 expected W25(p) (~a) to be a number.~%" (cell "W25")))
    (H5-)
    (incf w25p) ;; Start at W25+1 (per manual)
    (loop until (= w25p 80) 
	  ;; WWW OBIWON !!! The only place I should have to correct this is here (I hope!) 
	  as char = (aref *W24-Line-Buffer* (1- w25p))
	  do 
	  (!! :run-full "Deep in J183/4-Scanner: w25p = ~a, char = ~s~%" w25p char)
	  (when (case mode
		  (:blank (char-equal char #\space))
		  (:non-blank (not (char-equal char #\space)))
		  (t (error "!!! J183/4-Scanner given unknown mode: ~s" mode)))
	    (numset counter w25p)
	    (H5+)
	    (return t))
	  (incf w25p)
	  )
    ))

(defun scan-input-into-*W24-Line-Buffer* (line)
  (loop for c across line
	as p from 0 by 1
	do (setf (aref *W24-Line-Buffer* p) c))
  (!! :jdeep "             .....Read into *W24-Line-Buffer*: ~s~%" *W24-Line-Buffer*))

(defun J2n=move-0-to-n-into-w0-wn (n)
  (loop for nn from 0 to n 
	as wcell-name in *w-cells*
	as HCell = (let ((top (H0))) (ipop "H0") top)
	do (ipop wcell-name) (ipush wcell-name (cell-symb HCell))))

(defun J3n=restore-wn (n)
  (loop for nn from 0 to n as wname in *w-cells* do (ipop wname)))

(defun J4n=preserve-wn (n)
  (loop for nn from 0 to n as wname in *w-cells* do (ipush wname)))

(defun J5n=preserve-wn-then-move-0-n-into-w0-wn (n)
  (J4n=preserve-wn n)
  (J2n=move-0-to-n-into-w0-wn n)
  )

(defvar *copy-list-collector* nil)

(defun copy-ipl-list-and-return-head (head)
  (setf *copy-list-head-collector* nil)
  (copy-ipl-list (cell head) head)
  (print (list "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" *copy-list-head-collector*))
  *copy-list-head-collector*
 )

;;; The head symbol is used to tell when we need to store the new cell
;;; because it's the new head for returning to the caller. (FFF %%%
;;; UUU)

(defun copy-ipl-list (cell-or-symb/link &optional head-symbol)
  (cond
    ;; If you're handed a cell, create a new one
    ((cell? cell-or-symb/link)
     (let* ((new-name (newsym))
	    (new-cell (make-cell! :name new-name
				  :symb (copy-ipl-list (cell-symb cell-or-symb/link))
				  :link (copy-ipl-list (cell-link cell-or-symb/link)))))
       (when head-symbol (setf *copy-list-head-collector* new-cell))
       new-name))
    ;; If you get a zero, just return it to get pluged back in.
    ((zero? cell-or-symb/link) "0")
    ;; If it's a local symbol, create a new cell with a new symbol and copy the cell,
    ;; recursing for the symb and links
    ((local-symbol? cell-or-symb/link)
     (let* ((cell (cell cell-or-symb/link))
	    (new-name (newsym))
	    (new-cell (make-cell! :name new-name
				  :symb (copy-ipl-list (cell-symb cell))
				  :link (copy-ipl-list (cell-link cell)))))
       (when head-symbol (setf *copy-list-head-collector* new-cell))
       new-name))
    ;; If we're handed a global symbol or a number, just return it.
    ((or (numberp cell-or-symb/link)
	 (global-symbol? cell-or-symb/link))
     cell-or-symb/link)
    (t (break "In copy-ipl-list got ~s which wasn't expected." cell-or-symb/link))))

(defun copy-list-structure (l)
  (if (zero? l) l ;; End of sublist, just return the EOsL "0"
      (let ((new-name (newsym)))
	(setf (gethash new-name *symtab*) (mapcar #'copy-list-cell l))
	new-name)))

(defun copy-list-cell (cell)
  (if (zero? cell) cell ;; End of sublist, just return the EOsL "0"
      (let* ((new-cell (copy-cell cell)))
	(setf (cell-name new-cell) (newsym))
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

(defun pll (symb) (print-linear-list symb))
(defun print-linear-list (symb &optional (depth 0))
  (let ((cell (<== symb)))
    (if (> depth 5) (break "PRINT-LINEAR-LIST appears to be in a recursive death spiral!"))
    (format t "~%+------------------------- ~s [~a] -------------------------+~%" symb depth)
    ;; FFF Maintain depth and indent.
    (when (not (zero? (cell-symb cell)))
      (format t "| Description list:~%")
      (print-linear-list (cell-symb cell) (1+ depth)))
    (loop do (format t "| ~s~70T|~%" cell)
	  (let ((link (cell-link cell)))
	    (if (zero? link) (return :end-of-list))
	    (setf cell (cell link))))
    (format t "+--------------------------End: ~a -------------------------------------------+~%" symb)
    ))

(defun pl (symb &rest args)
    (format t "~%+------------------------- ~s ~s -------------------------+~%" symb (cell symb))
    (apply #'print-list symb args)
    (format t "+--------------------------End ~s -------------------------------------------+~%" symb)
    )
(defun print-list (symb &key (depth 0) (limit 10) (dls? t))
  (cond ((> depth limit) (format t "~a[@~a...]~%" (blanks (* (1- depth) 3)) depth))
	((or (not (atom symb)) (numberp symb) (null symb) (null (ignore-errors (cell symb))) (zero? symb)))
	(t (let ((cell (cell symb)))
	     (format t "~a(~a) ~s~%" (blanks (* depth 3)) depth
		     (or (gethash cell *jfn->name*) cell))
	     (when (cell? cell)
	       ;; Break direct recursions, don't chase numbers, and maybe don't chase DLs
	       (if dls?
		 (unless (equal (cell-symb cell) symb)
		   (print-list (cell-symb cell) :depth (1+ depth) :limit limit))
		 (format t "~a(dl suppressed)~%" (blanks (* (1+ depth) 3))))
	       (unless (equal (cell-link cell) symb)
		 (print-list (cell-link cell) :depth (1+ depth) :limit limit)))))))
	     
(defun pretty-print-cell (cell)
  (setf cell (<=! cell))
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
  (ipl-eval start-symb)
  (if (member :end-dump *!!*) (report-system-cells t))
  )

(defun initialize-machine ()
  (setf *running?* nil)
  (create-system-cells) ;; See above in storage section
  (H5+) ;; Init H5 +
  (setf (H3-cycles) 0 (cell-pq (cell "H3")) "01") ;; Init H3 Cycle-Counter
  (setf *W24-Line-Buffer* (Blank80)) ;; Init Read Line buffer
  (w25-init) ;; I/O pointer
  (w26-init) ;; Trap action list (actually ignored, but needed for most complex code to work.)
  (setf *genstack* nil)
  (clrhash *jfn-calls*)
  )

;;; Trap action list (actually ignored, but needed for most complex code to work.)
(defun w26-init ()
  (make-cell! :name "W26" :symb (cell-name (make-cell! :name (newsym "W26") :symb "0" :link "0"))))

(defun pq-explain (cell)
  (when (and (cell? cell) (stringp (cell-pq cell)))
    (second (assoc (cell-pq cell) *pq-meanings* :test #'string-equal))))

(defparameter *pq-meanings*
  '(
    ("" "Execute fn named by symb name itself")
    ("  " "Execute fn named by symb name itself")
    ("00" "Execute fn named by symb name itself")
    ("01" "Execute fn in cell named by symb")
    ("04" "Execute fn named in symb name itself (==00)")
    ("10" "Push the symb (name) itself on H0")
    ("11" "Push cntnts of the cell named by symb, onto H0")
    ("12" "Push 2nd deref on H0")
    ("13" "Push the symb (name) itself on H0 (==10)")
    ("14" "Push the symb (name) itself on H0 (==10)")
    ("20" "Move H0 to the named symbol itself and pop H0")
    ("21" "Move H0 to the cell named by symb, and pop H0")
    ("30" "Pop the named stack itself")
    ("31" "Pop the stack of the sym in the named cell")
    ("32" "Pop the stack of the 2nd derefed cell")
    ("40" "Push down (preserve) the named symb itself")
    ("50" "Replace H0 by the named symb itself")
    ("51" "Replace H0 by the cell named in the H0 symb")
    ("52" "Replace H0 2nd deref")
    ("60" "Copy of (0) replaces S; S lost; H0 n.c.") ;; Was (wrongly?): Set the symb name itself to H0")
    ("64" "Copy of (0) replaces S; S lost; H0 n.c. (==60)")
    ("70" "Goto by H5: -symb|+link itself")
    ))

;;; !!! WWW There's this screw case for popping the H0 arg stack which
;;; is when the JFns use H0 per se as an argument, or if it is
;;; indirect, because once the pop takes place, the cell called H0 has
;;; a new value (specifically, what used to be the top of its stack)
;;; I've thought about ways to do this by some sort of macro that
;;; creates a block and only does the pop at the end, but remember the
;;; results get pushed, so really we need to pop just before pushing
;;; the results. Ugh. So each Jfn needs to judiciously pop the
;;; arguments after whatever computation has been done to compute the
;;; new arguments. !!! This check isn't a guarantee bcs the use of H0
;;; could be indirect.

(defun check-jfn-arglist-for-red-flags*** (args)
  (if (member "H0" args :test #'string-equal)
      (format t "WARNING: @~a H0 is passed as a per se argument: ~s! WATCH OUT FOR H0 POP RACE!~%" (h3-cycles) args))
  args)

(defun ipl-eval (start-symb &aux s)
  (!! :run "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv Entering IPL-EVAL at ~s~%" start-symb)
  (prog (cell pq q p symb link)
     (ipush "H1" "exit")
     (ipush "H1" start-symb) ;; Where we're headed this time in.
     ;; Indicates (local) top of stack for hard exit (perhaps to recursive call)
   INTERPRET-Q 
     (!! :run-full "---> At INTERPRET-Q w/H1 = ~s! (*fname-hint* = ~s)~%" (H1) *fname-hint*)
     ;; H1's symb contains the name of the cell holding the
     ;; instruction to be interpreted. At this point it could be a
     ;; symbol or a list. If it's a symbol, we need to de-reference it
     ;; to the list. In the case of an internal (J) funtion this will
     ;; be a lambda, in which case we just call it and then advance
     (when (null (H1)) (break "!!! (H1) is NIL! Maybe missing a JFn definition?"))
     (let* ((fn (if (functionp (cell-symb (h1))) (cell-symb (h1))
		    (if (functionp (cell (cell-symb (h1)))) (cell (cell-symb (h1)))))))
       (when fn 
	 (let* ((arglist (second (function-lambda-expression fn)))
		(args (if (null arglist) ()
			  (check-jfn-arglist-for-red-flags***
			   (cons (cell-symb (H0))
				 (loop for arg in (cdr arglist)
				       as val in (h0+)
				       collect (cell-symb val)))))))
	   (when *fname-hint* 
	     (!! :jcalls (format t (if arglist "   .......... Calling ~a [~a]: ~s=~s~%"
				    "   .......... Calling ~a [~a] (No Args)~*~*~%")
			      *fname-hint* (getf (gethash *fname-hint* *jfn-plists*) 'explanation) arglist args))
	     (push args (gethash *fname-hint* *jfn-calls*)) ;; For (rj) summary reports
	     (maybe-break? *fname-hint*)
	     (setf *fname-hint* nil)
	     )
	   (apply fn args))
	 (ipop "H1") ;; Remove the JFn call
	 (go ADVANCE)
	 ))
     (setq cell (cell (cell-symb (H1)))) ;; This shouldn't be needed since we're operating all in cell now.
     ;(!! :run "@~a~a >>>>> ~s (~a) ~a~%" (H3-cycles) (H5) cell (pq-explain cell) (prettify-jexps-if-any cell))
     (!! :run "@~a~a >>>>> ~s (~a)~%" (H3-cycles) (H5) cell (pq-explain cell))
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
       (0 (setf S symb) (go INTERPRET-P))
       ;; 1 Take the name the symbol is pointing to ???? THIS IS WRONG?
       (1 (setf S (cell-symb (cell symb))) (go INTERPRET-P))
       ;; 2 Take the symbol in the cell at the name that the symb is pointing to 
       (2 (setf S (cell-symb (cell (cell-symb (cell symb))))) (go INTERPRET-P))
       (3 (!! :run "(Unimplemented monitor action in ~s; Executing w/o monitor!)~%" cell) (setf S symb) (go INTERPRET-P))
       (4 (!! :run "(Unimplemented monitor action in ~s; Executing w/o monitor!)~%" cell) (setf S symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go ASCEND)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!" cell))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!" cell))
       )
   INTERPRET-P 
     (!! :run-full "     -----> At INTERPRET-P w/P = ~s, S=~s~%" p S)
     (!! :s "     -----> At INTERPRET-P w/P = ~s, S=~s~%" p S) ;; FFF Allow the keys to be a list
     (case p
       (0 (go TEST-FOR-PRIMITIVE))
       (1 (ipush "H0" S))                    ;; Input S (after preserving HO)
       (2
	;; (!! :s "************************* (cell S) = ~s, (H0) = ~s~%" (cell s) (H0))
	(setf (cell-symb (cell S)) (cell-symb (H0))) (ipop "H0")) ;; 2=Output to S (then restore HO)
       (3 (ipop S))                         ;; Restore (pop up) S 
       (4 (ipush S))                         ;; Preserve (push down) S
       ;; 5: REPLACE (0) BY S. A copy of S is put in HO; the current (0) is lost.
       (5 (ipop "H0") (ipush "H0" S))
       ;; A copy of (0) is put in S; the current symbol in S is lost, and (0) is unaffected.
       (6 (ipop S) (ipush S (cell-symb (H0)))) 
       (7 (go BRANCH)) ;; Branch to S if H5-
       )
     (go ADVANCE)
   TEST-FOR-PRIMITIVE 
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (!! :run-full "-----> At TEST-FOR-PRIMITIVE w/S = ~s, Q = ~s, symb=~s~%" S q symb)
     (case q 
       (5 (setf link S) (go ADVANCE))
       (t (go DESCEND)))
   ADVANCE (!! :run-full "-----> At ADVANCE")
     (trace-cells)
     (if (and *adv-limit* (zerop (decf *adv-limit*)))
	 (break " !!!!!!!!!!!!!! IPL-EVAL hit *adv-limit* !!!!!!!!!!!!!!~%"))
     (incf (H3-cycles))
     (when (string-equal (cell-symb (h1)) "exit")
       (ipop "H1") ;; Remove the exit flag
       (!! :run "Exiting from IPL-EVAL ^^^^^^^^^^^^^^^^^^^^^^^^^^^~%")
       (return))
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (cell-link (cell (cell-symb (H1))))) ;; !!!!!!!! UGH !!!!!!!!
   ADVANCE-W/FORCED-LINK (!! :run-full "-----> At ADVANCE-W/FORCED-LINK (link=~s)~%" link)
     (setf *fname-hint* link)
     (clean-stacks)
     ;; If link is nil ("") in the middle of a function, go next cell, else ascend.
     (if (zero? link) (go ASCEND))
     ;; Note that if there is a link to a different function (commonly
     ;; J8 or J31, which resets H0 and W0+W1 respectively), then when
     ;; THAT function terminates the whole prog sequence ascends. This
     ;; is a somewhat confusing yet common way to end a function, that
     ;; is, by branching off to a J function which, when it completes,
     ;; pops to whereever its caller came from.
     (setf (cell-symb (h1)) link)
     (go INTERPRET-Q)
   ASCEND 
     (!! :run-full "-----> At ASCEND w/H1 = ~s~%" (h1))
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (ipop "H1")
     (go ADVANCE)
   DESCEND 
     (!! :run-full "-----> At DESCEND w/S = ~s~%" S)
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (setf *fname-hint* S)
     (ipush "H1" (cell S))
     (trace-cells)
     (go INTERPRET-Q)
   BRANCH
     (!! :run-full "-----> At BRANCH w/H5 = ~s, S= ~s~%" (H5) S)
     ;; Interpret Sign in H5: - H5-: Put S as LINK (control transfers to S); go
     ;; to ADVANCE. - H5+: Go to ADVANCE
     (when (string-equal (H5) "-") (setf link S) (go ADVANCE-W/FORCED-LINK))
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
  (push s *card-ids-executed*)
  (when (or (equal t *breaks*)
	    (member t *breaks*)
	    (member (H3-cycles) *breaks* :test #'equal)
	    (member s *breaks* :test #'equal))
    (break "************************** Break called by user at ~s (BEFORE execution!)~%[Switching to STEP! mode -- use :C to step or (free!)+:C to run free." s)
    (step!)
    (report-system-cells t)))

;;; =========================================================================
;;; Large printer

(defparameter *letters*
  (loop for (let . whomp) in 
	'(("a" . ("###" "# #" "###" "# #" "# #"))
	  ("b" . ("###" "# #" "###" "# #" "###"))
	  ("c" . ("###" "#" "#" "#" "###"))
	  ("d" . ("##" "# #" "# #" "# #" "##"))
	  ("e" . ("###" "#" "###" "#" "###"))
	  ("f" . ("###" "#" "###" "#" "#"))
	  ("g" . ("###" "# #" "###" "  #" "###"))
	  ("h" . ("# #" "# #" "###" "# #" "# #"))
	  ("i" . ("###" " #" " #" " #" "###"))
	  ("j" . ("###" " #" " #" " #" "##"))
	  ("k" . ("# #" "##" "#" "##" "# #"))
	  ("l" . ("#" "#" "#" "#" "###"))
	  ("m" . ("# #" "###" "###" "# #" "# #"))
	  ("n" . ("###" "# #" "# #" "# #" "# #"))
	  ("o" . ("###" "# #" "# #" "# #" "###"))
	  ("p" . ("###" "# #" "###" "#" "#"))
	  ("q" . ("###" "# #" "## " " # " " ##"))
	  ("r" . ("###" "# #" "##" "# #" "# #"))
	  ("s" . ("###" "#" "###" "  #" "###"))
	  ("t" . ("###" " #" " #" " #" " #"))
	  ("u" . ("# #" "# #" "# #" "# #" "###"))
	  ("v" . ("# #" "# #" "# #" "# #" " #"))
	  ("w" . ("# #" "# #" "# #" "###" "###"))
	  ("x" . ("# #" " #" " #" " #" "# #"))
	  ("y" . ("# #" "# #" " # " " # " " # "))
	  ("z" . ("###" "  #" " #" "#" "###"))
	  (" " . (" "))
	  ("1" . (" #" "##" " #" " #" "###"))
	  ("2" . ("## " "  #" " # " "#  " "###"))
	  ("3" . ("###" "  #" " ##" "  #" "###"))
	  ("4" . ("#" "#" "# #" "###" "  #"))
	  ("5" . ("###" "#" "###" "  #" "###"))
	  ("6" . ("###" "#" "###" "# #" "###"))
	  ("7" . ("###" "  #" " # " " # " "#  "))
	  ("8" . ("###" "# #" "###" "# #" "###"))
	  ("9" . ("###" "# #" "###" "  #" "  #"))
	  ("0" . ("###" "# #" "# #" "# #" "###"))
	  ("!" . (" # " " # " " # " " " " # "))
	  ("?" . ("###" " #" " ##" " " " # "))
	  ("-" . (" " " " "###" " " "   "))
	  ("+" . (" # " " # " "###" " # " " # "))
	  ("." . (" " " " " " " " " # "))
	  ("(" . (" # " "#  " "#  " "#  " " # "))
	  (")" . (" # " "  #" "  #" "  #" " # "))
	  ("/" . ("  #" " # " " # " " # " "# "))
	  ("*" . ("# #" " # " "### " " # " "# #"))
	  (":" . (" " " # " " " " # " " "))
	  ("=" . ("   " "   " "###" " " " "))
	  ("'" . (" # " " # " " " " " " "))
	  ("#" . (" # " "###" " # " "###" " # ")))
	collect (cons let (mapcar #'(lambda (whimp) (substitute (char-upcase (aref let 0)) #\# whimp)) whomp))))

(defun print-letters (text &optional (scale 1) (espace 2))
  (let ((bigletters '()))
    ;; Get letter patterns for each character
    (loop for i across text
          do (push
	      (or (cdr (assoc (string-downcase (string i)) *letters* :test #'string=))
		  (cdr (assoc " " *letters* :test #'string=)))
              bigletters))
    (setf bigletters (reverse bigletters))
    ;; Create output lines
    (let ((output (make-list (* 5 scale) :initial-element "")))
      (loop for i from 0 below 5
            do (loop for ind from 0 below (length bigletters)
                     for j = (nth ind bigletters)
                     do (let ((temp " "))
                          (if (and j (< i (length j)))
                              (setf temp (nth i j))
                              (setf temp " "))
                          (let ((line ""))
                            ;; Scale horizontally
                            (loop for z across temp
                                  do (dotimes (s scale)
                                       (setf line (concatenate 'string line (string z)))))
                            ;; Add spacing
                            (setf line (concatenate 'string line 
                                                    (make-string (- (+ (* 3 scale) espace) (length line)) 
                                                                 :initial-element #\Space)))
                            ;; Append to output line
                            (setf (nth (* i scale) output) 
                                  (concatenate 'string (nth (* i scale) output) line))
                            
                            ;; Create bold effect for scaling
                            (loop for bold from 1 below scale
                                  do (setf (nth (+ (* i scale) bold) output)
                                           (nth (* i scale) output)))))))
      (format nil "~{~A~^~%~}" output))))

(defun announce (fmt &rest args)
  (format t "~%~A~%" (print-letters (apply #'format nil fmt args) 1 1)))


;;; =========================================================================
;;; Test calls

;;; Reminders: rsc rsc* (pll list-head-cell)

;;; Basic tracing setup for "light" tracing.

(defun set-default-tracing ()
  (untrace)
  (setf *trace-cell-names* nil)
  (setf *breaks* nil) ;; If this is set to t (or '(t)) it break on every call
  (setf *stack-depth-limit* 25) ;; (Nb. must be much higher, ~100, for Ackermann!)
  (setf *!!* *default-!!list*) 
  (setf *report-all-system-cells?* nil)
  (setf *cell-tracing-on* nil)
  (setf *trace-@orID-exprs* nil)
  (trace ipl-eval))

;; Comment (or just ') progn blocks out as needed.

(progn ;; F1 test
  (set-default-tracing)
  (setf *!!* '() *cell-tracing-on* nil)
  ;(setf *!!* '(:run :jdeep :jcalls) *cell-tracing-on* t)
  ;(push :run-full *!!*)
  ;(trace functionp ipush ipop iset data-set)
  ;(setf *trace-cell-names* '("H0" "H1" "W0" "W1") *cell-tracing-on* t)
  (load-ipl "F1.lisp")
  )

(progn ;; Ackermann test
  (set-default-tracing)
  (setf *!!* '() *cell-tracing-on* nil *stack-depth-limit* 100)
  ;(setf *trace-cell-names* '("H0" "K1" "M0" "N0") *cell-tracing-on* t)
  ;(setf *trace-@orID-exprs* '((9 (break))))
  ;(setf *!!* '(:run :jdeep) *cell-tracing-on* t)
  ;(trace ipop poph0)
  (load-ipl "Ackermann.iplv" :adv-limit 25000)
  (print (cell "N0"))
  (if (= 61 (cell-link (cell "N0")))
      (format t "~%*********************************~%* Ackerman (3,3) = 61 -- Check! *~%*********************************~%")
      (error "Oops! Ackermann (3,3) should have been 61, but was ~s" (cell "N0")))
  )

'(progn ;; Test of call stack state machine.
  (set-default-tracing)
  (setf *trace-cell-names* '("H0" "H1") *cell-tracing-on* t)
  (load-ipl "T123.lisp" :adv-limit 100)
  )

;;; WWW If this ends early with a BAD EXPRESSION (or other "normal
;;; error"), you're likely to get redisual errors from the loader
;;; trying to read more data after "normal" termination of the
;;; program.

#|

*1    ((AVA)IA)
+------------------------- "*1" {*1||9+2233|9+2252} -------------------------+
(0) {*1||9+2233|9+2252}
   (dl suppressed)
   (1) {9+2252||L+2245|0}
      (2) {L+2245|02|I0|9+2249}
         (3) {I000D000::I0||I0+1841|0 [IMPLIES;]}
            (4) {I000D010::I0+1841||0|I0+1842}
               (5) {I000D020::I0+1842||Q14|I0+1843}
                  (6) {Q014R000::Q14|10|Q14|J10 [Q14 FIND TYPE OF CONNECTIVE (0).;]}
                     (7) "J10"
                  (6) {I000D030::I0+1843||J4|I0+1844}
                     (7) "J4"
                     (7) {I000D040::I0+1844||Q7|I0+1845}
                        (8) {Q007R000::Q7|10|Q7|J10 [ATTRIBUTE--EXTERNAL NAME;]}
                           (9) "J10"
                        (8) {I000D050::I0+1845||I0+1846|0}
                           (9) {I000D060::I0+1846|21|I|}
         (3) {9+2249||L+2246|9+2250}
            (4) {L+2246|02|V0|9+2247}
               (5) {V000D000::V0||V0+2031|0 [OR;]}
                  (6) {V000D000::V0+2031||0|V0+2032}
                     (7) {V000D010::V0+2032||Q14|V0+2033}
                        (8) {Q014R000::Q14|10|Q14|J10 [Q14 FIND TYPE OF CONNECTIVE (0).;]}
                           (9) "J10"
                        (8) {V000D020::V0+2033||J4|V0+2034}
                           (9) "J4"
                           (9) {V000D030::V0+2034||Q7|V0+2035}
                              (10) {Q007R000::Q7|10|Q7|J10 [ATTRIBUTE--EXTERNAL NAME;]}
                              [@11...]
                              (10) {V000D040::V0+2035||V0+2036|0}
                              [@11...]
                              [@11...]
               (5) {9+2247||A0|9+2248}
                  (6) {A000D000::A0||A0+1782|0 [FREE VARIABLE A;]}
                     (7) {A000D010::A0+1782||0|A0+1783}
                        (8) {A000D020::A0+1783||Q5|A0+1784}
                           (9) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              (10) "J10"
                           (9) {A000D030::A0+1784||Q5|A0+1785}
                              (10) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              [@11...]
                              (10) {A000D040::A0+1785||Q6|A0+1786}
                              [@11...]
                              [@11...]
                  (6) {9+2248||A0|0}
                     (7) {A000D000::A0||A0+1782|0 [FREE VARIABLE A;]}
                        (8) {A000D010::A0+1782||0|A0+1783}
                           (9) {A000D020::A0+1783||Q5|A0+1784}
                              (10) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              [@11...]
                              (10) {A000D030::A0+1784||Q5|A0+1785}
                              [@11...]
                              [@11...]
            (4) {9+2250||A0|0}
               (5) {A000D000::A0||A0+1782|0 [FREE VARIABLE A;]}
                  (6) {A000D010::A0+1782||0|A0+1783}
                     (7) {A000D020::A0+1783||Q5|A0+1784}
                        (8) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                           (9) "J10"
                        (8) {A000D030::A0+1784||Q5|A0+1785}
                           (9) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              (10) "J10"
                           (9) {A000D040::A0+1785||Q6|A0+1786}
                              (10) {Q006R000::Q6|10|Q6|J10 [ATTRIBUTE-FREE VARIABLE;]}
                              [@11...]
                              (10) {A000D050::A0+1786||Q6|A0+1787}
                              [@11...]
                              [@11...]
+--------------------------End "*1" -------------------------------------------+



*2    ((PVP)IP)
+------------------------- "*2" {*2||9+2284|9+2303} -------------------------+
(0) {*2||9+2284|9+2303}
   (dl suppressed)
   (1) {9+2303||L+2296|0}
      (2) {L+2296|02|I0|9+2300}
         (3) {I000D000::I0||I0+1841|0 [IMPLIES;]}
            (4) {I000D010::I0+1841||0|I0+1842}
               (5) {I000D020::I0+1842||Q14|I0+1843}
                  (6) {Q014R000::Q14|10|Q14|J10 [Q14 FIND TYPE OF CONNECTIVE (0).;]}
                     (7) "J10"
                  (6) {I000D030::I0+1843||J4|I0+1844}
                     (7) "J4"
                     (7) {I000D040::I0+1844||Q7|I0+1845}
                        (8) {Q007R000::Q7|10|Q7|J10 [ATTRIBUTE--EXTERNAL NAME;]}
                           (9) "J10"
                        (8) {I000D050::I0+1845||I0+1846|0}
                           (9) {I000D060::I0+1846|21|I|}
         (3) {9+2300||L+2297|9+2301}
            (4) {L+2297|02|V0|9+2298}
               (5) {V000D000::V0||V0+2031|0 [OR;]}
                  (6) {V000D000::V0+2031||0|V0+2032}
                     (7) {V000D010::V0+2032||Q14|V0+2033}
                        (8) {Q014R000::Q14|10|Q14|J10 [Q14 FIND TYPE OF CONNECTIVE (0).;]}
                           (9) "J10"
                        (8) {V000D020::V0+2033||J4|V0+2034}
                           (9) "J4"
                           (9) {V000D030::V0+2034||Q7|V0+2035}
                              (10) {Q007R000::Q7|10|Q7|J10 [ATTRIBUTE--EXTERNAL NAME;]}
                              [@11...]
                              (10) {V000D040::V0+2035||V0+2036|0}
                              [@11...]
                              [@11...]
               (5) {9+2298||P0|9+2299}
                  (6) {P000D000::P0||P0+1916|0 [VARIABLE P;]}
                     (7) {P000D010::P0+1916||0|P0+1917}
                        (8) {P000D020::P0+1917||Q5|P0+1918}
                           (9) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              (10) "J10"
                           (9) {P000D030::P0+1918||Q5|P0+1919}
                              (10) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              [@11...]
                              (10) {P000D033::P0+1919||Q9|P0+1920}
                              [@11...]
                              [@11...]
                  (6) {9+2299||P0|0}
                     (7) {P000D000::P0||P0+1916|0 [VARIABLE P;]}
                        (8) {P000D010::P0+1916||0|P0+1917}
                           (9) {P000D020::P0+1917||Q5|P0+1918}
                              (10) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              [@11...]
                              (10) {P000D030::P0+1918||Q5|P0+1919}
                              [@11...]
                              [@11...]
            (4) {9+2301||P0|0}
               (5) {P000D000::P0||P0+1916|0 [VARIABLE P;]}
                  (6) {P000D010::P0+1916||0|P0+1917}
                     (7) {P000D020::P0+1917||Q5|P0+1918}
                        (8) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                           (9) "J10"
                        (8) {P000D030::P0+1918||Q5|P0+1919}
                           (9) {Q005R000::Q5|10|Q5|J10 [ATTRIBUTE-VARIABLE;]}
                              (10) "J10"
                           (9) {P000D033::P0+1919||Q9|P0+1920}
                              (10) {Q009R000::Q9|10|Q9|J10 [Q9 ATTRIBUTE--BOUND VARIABLE.;]}
                              [@11...]
                              (10) {P000D037::P0+1920||Q9|P0+1921}
                              [@11...]
                              [@11...]
+--------------------------End "*2" -------------------------------------------+


|#

#| Current problem and issues:

|#

;;; debugging tools: (pl cell) (pll cell) (rj) :c (rx)

'(progn ;; LT 
  (set-default-tracing)
  '(push :load *!!*)
  '(trace convert-local-symbols)
  '(setf *!!* nil *cell-tracing-on* nil)
  '(setf 
   *!!* '(:jfns :run :jcalls)
   *trace-cell-names* '("H0" "W0" "W1" "W2")
   *cell-tracing-on* t)
  '(setf *trace-@orID-exprs*
	'(;(440 (setf *!!* '(:s :jfns :run :jcalls :jdeep) *trace-cell-names* '("H0" "W0" "W1" "W2") *cell-tracing-on* t))
	  ;(460 (break))
	  (2000 (trace copy-list-cell copy-list-structure copy-ipl-list copy-ipl-list-and-return-head))
	  ;(2040 (setf *!!* '(:s :jfns :run :jcalls :jdeep) *trace-cell-names* '("H0" "W0" "W1" "W2") *cell-tracing-on* t))
	  ))
  (load-ipl "LTFixed.lisp" :adv-limit 5000)
  )

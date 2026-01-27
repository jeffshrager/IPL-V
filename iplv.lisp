;;; (load (compile-file "iplv.lisp"))

;;; I recovered to here after an errant exploration into using local
;;; symbol stacks instead of the (correct) general stack mechanism for
;;; storage cells.

(setf *print-pretty* nil)

;;; FFF Do something to simplify the various make-cells and
;;; cell-cell!s all over the place with different args.

;;; See notes.txt!

;;; WWW Leaves these at high debug etc or things break for unknown reasons.
(declaim (optimize (debug 3) (safety 3) (speed 0) (space 0) (compilation-speed 0)))

;;; ===================================================================
;;; Cell, Storage, and Special Symbols

(defstruct (cell (:print-function print-cell) (:predicate cell?))
  (comments "")
  (type "0")
  ;; The name actually isn't part of the cell, it's the address where
  ;; the cell lives. At stability (that is, not in the middle of a
  ;; function) this should always match the symbol table entry that
  ;; the cell lives in. In many (maybe most) cases we probably could
  ;; get this in another way, like passing in the cell's address
  ;; (name) along with the cell, and using that in process, but this
  ;; is simpler and more direct, although it is yet another thing to
  ;; go wrong! (Not having it would make push and pop way simpler, but
  ;; also harder to debug!)
  (name "") 
  (sign "0")
  (p 0)
  (q 0)
  (symb "0")
  (link "0")
  (comments.1 "")
  (id "")
  )

(defvar *symtab* (make-hash-table :test #'equal))

(defun newsym (&optional (prefix "9")) (string (gensym (concatenate 'string prefix "-"))))

(defun store (cell &optional (name (cell-name cell)))
  ;;(!! :dr-memory "== Store ==> ~s [mem]" cell) Causes compiler race condition
  (setf (gethash name *symtab*) cell)
  cell)
  
(defun make-cell! (&rest args)
  (let* ((name (getf args :name)))
    (store 
     (if name
	 (apply #'make-cell args)
	 (apply #'make-cell :name (newsym) args)))))

(defun zero? (what) (if (stringp what) (member what '("" "0") :test #'string-equal)))

(defun string-equal! (a b) ;; No-fail S-Eq ... a stupid impl. detail of CL!
  (when (and (stringp a) (stringp b))
    (string-equal a b)))

(defun blank? (what)
  (string-equal "" what))

(defun print-cell (cell s d)
  (declare (ignore d))
  (let ((p (cell-p cell)) (q (cell-q cell)))
    (if (and (zerop p) (zerop q))
	(format s "{~a~a||~a|~a~a}"
		(if (zero? (cell-id cell)) "" (format nil "~a::" (cell-id cell)))
		(cell-name cell) (cell-symb cell) (cell-link cell)
		(format-cell-comments-for-printing cell))
	(format s "{~a~a|~a~a|~a|~a~a}"
		(if (zero? (cell-id cell)) "" (format nil "~a::" (cell-id cell)))
		(cell-name cell) p q (cell-symb cell) (cell-link cell)
		(format-cell-comments-for-printing cell)))))

(defun format-cell-comments-for-printing (cell)
  (if (and (zero? (cell-comments cell)) (zero? (cell-comments.1 cell))) 
      "" (format nil " [~a;~a]" (cell-comments cell) (cell-comments.1 cell))))


;;; The generator triplex. The generator system maintains its own
;;; private stack, which is the "generator hideout" referred to in the
;;; manual and below where J17-19 are defj'ed.

(defvar *genstack* nil)
(defstruct gentry fn wn wnames +- gentag)

;;; =========================================================================
;;; DEBUGGING TOOLS

(defun ptbl (tbl)
  (loop for key being the hash-keys of tbl
	using (hash-value val)
	do (format t "~s :: ~s~%" key val)))

(defvar *trace-instruction* nil) ;; Used in error traps, so need to declare early.
(defvar *fname-hint* "") ;; for messages in the middle of jfn ops
(defvar *jfn-calls* (make-hash-table :test #'equal))
(defvar *jfn-plists* (make-hash-table :test #'equal))
(defvar *jfn-arg-traps* nil) ;; If anything in here get's passed to a jfn we hit a break.

;;; Find every reference to a given symbol in either the symtab or in
;;; lists (FFF add stack search):

(defun fsym (sym &key (print-lists? nil) &aux inlists)
  (format t "*symtab* and list-embedded references to ~s:~%" sym)
  (loop for name being the hash-keys of *symtab*
	using (hash-value cell)
	when (cell? cell)
	do (cond ((or (string-equal! sym name)
		     (string-equal! sym (cell-name cell))
		     (string-equal! sym (cell-symb cell))
		     (string-equal! sym (cell-link cell)))
		  (format t "  ~s -> ~s~%" name cell))
		 ((in-list? sym cell cell) (push cell inlists))))
  (if print-lists? 
      (progn (format t "Also in these lists: ~%~%")
	     (mapcar #'(lambda (cell) (pl (cell-name cell))) inlists))
      (progn (format t "Also in these lists (add :print-lists? t to see them pl'ed): ~%~%")
	     (mapcar #'print inlists)))
  t)

	
(defun in-list? (sym cell top-cell &optional (limit 50))
  (cond ((zerop limit) (format t "WARNING! ~s seems to head an infinite list!~%" top-cell))
	((global-symbol? cell) nil) ;; Don't chase global symbs
	((zero? cell) nil)
	((string-equal! sym cell) t)
	(t (let ((cell (<== cell)))
	     (and (cell? cell)
		  (or (in-list? sym (cell-symb cell) top-cell (1- limit))
		      (in-list? sym (cell-link cell) top-cell (1- limit))))))))

;;; This throws an annoying warning and is a non-critical deugging tool
'(defun rj () ;; report on jfns
  (let ((*print-length* nil))
    (loop for (jname ncalls expl argcounts) in
	  (sort (loop for jname being the hash-keys of *jfn-calls*
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

(defvar *card-cycles.ids-executed* nil)
(defvar *rxtbl* (make-hash-table :test #'equal))

(defparameter *checked-routines*
  '(
    "M001" "M002" "M003" "M012" "M042" "M043" "M050"
    "M054" "M062" "M063" "M070" "M072" "M073" "M074"
    "M079" "M089" "M111" "P004" "P006" "P007" "P008"
    "P009" "P015" "P018" "P019" "P027" "P029" "P031"
    "P050" "P051" "P052" "P055" "Q001" "Q002" "Q005"
    "Q006" "Q007" "Q008" "Q009" "Q010" "Q011" "Q012"
    "Q013" "Q014" "Q015" "Q016" "Q017" "Q018" "Q019"
    "X001" "Q004" "Q003" "P030" "P028" "M116" "M115"
    "M114" "M110" "M088" "M082" "M080" "M078" "M077"
    "M076" "M071" "M071" "P014" "M112" "M113" "P024"
    "P017" "P013" "P016" "P000" "M041" "M040" "M019"
    "M017" "M016" "M014" "P022" "J73"  "J74"  "M008"
    "M013" "M007" "M011" "M015" "M051" "M075" "M090"
    "P025" "P003" "P026"))

(defun trace! ()
  (loop for entry in (reverse *card-cycles.ids-executed*)
  	with indent = 0
   	do
   	(if (listp entry) (format t "~vT~s~%" indent entry)
   	    (if (eq :descend entry) (incf indent 3) (decf indent 3)))))
(defun backtrace! (&optional (n 10))
  (loop for entry in *card-cycles.ids-executed*
	as k below n
  	with indent = 0
   	do
   	(if (listp entry) (format t "~vT~s~%" indent entry)
   	    (if (eq :descend entry) (incf indent 3) (decf indent 3)))))

(defun rx () ;; report on execs (card ids executed)
  (clrhash *rxtbl*)
  (loop for entry in *card-cycles.ids-executed*
	as id = (when (listp entry) (cdr entry))
	if (and id (stringp id) (= 8 (length id)))
	do (incf (gethash (subseq id 0 4) *rxtbl* 0)))
  (format t "~%~%All call stats:~%")
  (let ((callstats (loop for rname being the hash-keys of *rxtbl*
		 using (hash-value nx)
		 collect (cons rname nx))))
    ;; This throws an annoying warning and is a non-critical deugging tool
    ;(mapcar #'print (sort callstats #'string< :key #'car))
    (format t "~%~%Unchecked calls:~%")
    (mapcar #'print (SET-DIFFERENCE (mapcar #'car callstats) *checked-routines* :TEST #'STRING-EQUAL))))

(defvar *cell-tracing-on* nil)
;;; These will get eval'ed at the given id, for example:
;;;   ("P051R050" (print "hello"))
;;; or, more reasonably:
;;; ("P051R050" (setf *trace-cell-names-or-exprs* '("W0" "W1" "H0" "H5") *cell-tracing-on* t))
;;; If the ID is a number rather than a string, it refers to the value in (H3)
(defvar *trace-exprs* nil) 
(defvar *breaks* nil) ;; If this is set to t it breaks on every call
(defvar *trace-cell-names-or-exprs* nil) 

(defun step! () (setf *breaks* t) "Use :c to step.")
(defun free! (&optional next-breaks) (setf *breaks* next-breaks) "Use :c to run free.")

;; ;;; Search a list (given the head cell's name) for a specific symbol,
;; ;;; and eval the action when it's found. This is usually used to throw
;; ;;; breaks when something weird gets put into a list.

;; (defun act-on-symbol-in-list (action symbol head-name)
;;   (when (search-ipl-list-for head-name symbol)
;;     (eval action)))

;; (defun search-ipl-list-for (cell-name symbol &optional (depth 0))
;;   (when (and (< depth 50) (stringp cell-name) (not (zero? cell-name)))
;;     (let* ((cell (<== cell-name))
;; 	   (symb (cell-symb cell)))
;;       (print (list cell-name cell symb))
;;       (cond ((and (stringp symb) (string-equal symbol symb)) t)
;; 	    (t (search-ipl-list-for symb symbol (1+ depth))
;; 	       (search-ipl-list-for (cell-link cell) symbol (1+ depth)))))))

;;; =========================================================================
;;; ACCESSORS

;;; Dereferencing versions of cell struct accessors. Cell is macro for
;;; stacked symbols, like H0 and W0, used where there isn't a special
;;; macro for common ones.  WWW Note the convention of adding + when
;;; the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot
;;; try to push/pop things that aren't stacks!

(defmacro cell (symb) `(gethash ,symb *symtab*))

(defvar *!!* nil) 

(defmacro H3-cycles () `(cell-link (cell "H3")))

(defmacro !! (key &rest args) 
  `(when (or (equal *!!* t)
	     (equal ,key t)
	     (member ,key *!!*))
     ;; There's a special hack here for :run just to make it slightly prettier
     ,(if (stringp (car args))
	  (if (member key '(:load :run))
	      `(format t ,(car args) ,@(cdr args)) ;; Run already puts this info out
	      `(format t (concatenate 'string ,(car args) " % ~a@~a[~a]~%") ,@(cdr args) *fname-hint* (h3-cycles) ,key))
	  `(progn ,@args))))

;;; Cell dereferencing: Used when you need a cell. <=! is more
;;; powerful in that it can create the cell if it's not found, and is
;;; slightly heuristic. <== should be used where possible, and only
;;; use <=! when you need the heuristication and/or auto-creation.

(defun <== (cell-or-symb)
  (!! :dr-memory "<== retreiving ~s" cell-or-symb)
  (if (cell? cell-or-symb) cell-or-symb (gethash cell-or-symb *symtab*)))

(defun <=! (cell-or-symb &key create-if-does-not-exist?) ;; cell-or-symb can be a cell or a name
  (!! :dr-memory "<=! retreiving ~s" cell-or-symb)
  (or (<== cell-or-symb)
      (if (stringp cell-or-symb)
	  (if create-if-does-not-exist?
	      (let ((new-cell (make-cell! :name cell-or-symb)))
		(!! :dr-memory "<=! created ~s" new-cell)
		new-cell)
	      (error "In <=! ~s isn't a cell and you didn't ask to create it!"
		     cell-or-symb)))))

(defmacro cell-name% (cell-or-symb)
  `(cell-name (<== ,cell-or-symb)))
(defmacro cell-symb% (cell-or-symb)
  `(cell-symb (<== ,cell-or-symb)))

;;; Important values have special macros (these are like (H0) = (0) in
;;; the IPL-V manual). The ...+ fns return the whole stack. (Note that
;;; you'll have to get (1), that is, the second stack entry in H0
;;; manually!)

(defmacro H0 () `(<== "H0"))
(defmacro H0+ () `(<== (cell-link (H0)))) ;; This is the cell AFTER H0 (it's underlying stack)

;;; Input/Push to system stack: This creates a copy only of the
;;; CONTENTS of the system cell.

;;; WWW DESTRUCTIVE!!! MAKE SURE YOU'RE DOING IT TO A CLEAN CELL!!!
(defun data-set (curcell &key (sign "0") (p 0) (q 0) (symb "") (link "0") (id ""))
  (!! :dr-memory "WWW DATA-SET IS DESTRUCTIVELY HACKING ~s " curcell)
  (setf (cell-sign curcell) sign
	(cell-p curcell) p
	(cell-q curcell) q
	(cell-symb curcell) symb
	(cell-id curcell) id
	(cell-link curcell) link
	)
  (!! :dr-memory " TO: ~s" curcell)
  curcell)

;;; IPUSH and IPOP are the core functions of the machine. They
;;; push/pop cells onto IPL lists that begin with the indicated
;;; symbol. This is used for the storage cell mostly, but also in some
;;; cases when non-storage cell lists are treated as stacks (for
;;; example, the PQ=31 screw case at M062R660). Note that these work
;;; only on NON-DESCRIBLE SIMPLE LISTS, that is, where the head cell
;;; contains the head symbol, not a 0, or description list. If no
;;; newval is given, the top symbol is copied down to the pushed
;;; cell. Note that we don't need to copy anything but the
;;; symbol. There are certain cases where other elements of the
;;; stacked cell are tested (for example in stack process marking and
;;; testing -- J133 and J137 -- but these marks get added and tested
;;; by those functions, and only need to be on top. They get popped
;;; off with the top cell. Thus when we PUSH we need to actually
;;; rename the top cell and stick it back into the symbol table under
;;; the new name, and then create a new top cell, and put THAT into
;;; the symbol table where the old top cell was. (Alt. we could copy
;;; all the contents down.) But POPPING is easier, but all of this
;;; takes a little but of care with adding and removing things to/from
;;; the symtab. There is a slight infelicitude when the first push
;;; happens because if the symbol of the head is zero, we just set the
;;; symbol, not push a new cell, because that would make there be a
;;; zero in the head.

(defun ipush (stack-name &optional newval)
  (!! :dr-memory "Entering IPUSH, ~a = ~a" stack-name (getstack stack-name))
  (let* ((old-head-cell (<== stack-name))
	 (newval (or newval (cell-symb old-head-cell))))
    ;; Immediately see if we can just smash the 0 in the current head.
    (if (zero? (cell-symb old-head-cell))
	(progn 
	  (!! :dr-memory "IPUSHing ~a into the blank stack: ~a" newval stack-name)
	  (setf (cell-symb old-head-cell) newval))
	(let* (
	       ;; This will be the new name of the old head cell, and will be linked
	       ;; from the new head cell.
	       (new-second-entry-name (newsym))
	       (new-head-cell
		;; WWW This is safe, but looks dangerous becasue it's replacing the
		;; old head, but we're aleady holding on to it just above.
		(make-cell! :name stack-name :symb newval :link new-second-entry-name)))
	  (!! :dr-memory "IPUSHing ~a into ~a" newval stack-name)
	  (!! :dr-memory "   ... old head=~a, new-head=~a" old-head-cell new-head-cell)
	  ;; Now all we should have to do is jam the new second-entry which is just
	  ;; the renamed old-head-cell into the symtab.
	  (setf (cell-name old-head-cell) new-second-entry-name)
	  (!! :dr-memory "   ... storing renamed old-head-cell: ~a" old-head-cell)
	  (store old-head-cell)))
    (!! :dr-memory "Exiting IPUSH, ~a = ~a" stack-name (getstack stack-name))
    ;; No one should be using this result!
    :!ipush-result!))

;;; IPOP is simpler: It just stores the old second entry in the list back into
;;; the head named symbol. (For possible error tracking, we smash the name of
;;; the old head, although it should be lost and eventually GC'ed, but if it
;;; shows up, we know something went really wrong!)

(defun ipop (stack-name)
  (!! :dr-memory "Entering IPOP, ~a = ~a" stack-name (getstack stack-name))
  (let* ((old-head (<== stack-name))
	 (head-link (cell-link old-head)))
    ;; If this is the top of the stack, the link will be 0. In this
    ;; case we just replace the symbol with "0" and the stack is
    ;; empty.
    (if (not (zero? head-link))
	;; There's more to the stack:
	(let* ((new-head (<== head-link )))
	  (setf (cell-name new-head) stack-name)
	  (store new-head)
	  (setf (cell-name old-head) (format nil "BAD POP OF ~a @ ~a" stack-name (h3-cycles)))
	  (!! :dr-memory "IPOP created new head: ~a (old head: ~a)" new-head old-head)
	  )
	;; The stack is empty (link = "0"):
	(progn 
	  (setf (cell-symb old-head) "0") ;; Link should already be zero (I hope!)
	  (!! :dr-memory "IPOP cleared stack: ~a" old-head)))
    (!! :dr-memory "Exiting IPOP, ~a = ~a" stack-name (getstack stack-name))
    ;; No one should be using this result!
    :!ipop-result!))

;;; This is used in JFns to deref args H0

(defmacro H1 () `(cell "H1")) ;; WWW DO NOT CONFUSE H1 with (1) !!!
(defmacro H1+ () `(stack "H1")) ;; WWW DO NOT CONFUSE H1 with (1) !!!

;;; WWW H5 MUST be set using these functions!

(defmacro H5 () `(cell-symb (cell "H5")))
(defmacro H5+ () `(setf (H5) "+"))
(defmacro H5- () `(setf (H5) "-"))

;;; This can trace strings, or any element (name/symb/link) of a cell
;;; incl. stackables.

(defvar *running?* nil)

;;; Example usage of *trace-exprs*
;;;   ("P051R050" (setf *trace-cell-names-or-exprs* '("W0" "W1" "H0" "H5") *cell-tracing-on* t))
;;;   ("P051R050" (setf *!!* '(:run :run-full :jdeep)))
;;; Can also be a number in which case it refers to the H3 value (@), as:
;;;   (123 ...)
;;; WWWWWWW Must call (trace-cell-safe-for-trace-expr) or (???) to trace cells otherwise messy recusion cycle ensues
;;; (setf *trace-exprs*
;;;    '(("P052R040" ;; NOTE: This can be partial, as "P052R" it uses search **************
;;;       (setf *trace-cell-names-or-exprs* '("W0" "W1" "H0") *cell-tracing-on* t)
;;;       (trace symbolify ipl-string-equal ipl-string-equal))
;;;      (123 (trace) (setf *cell-tracing-on* nil *!!* *default-!!list*))
;;;      ))
;;; The key can be a partial string (it uses search) a number (indicating H3 cycles)
;;; or a list which is simple evaled

(defvar *stack-display-depth* 4)

(defun trace-cells ()
  (let* ((cycle (h3-cycles))
	 (id (cell-id *trace-instruction*)))
    (mapcar #'eval
	    (loop for (key . exprs) in *trace-exprs*
		  if (or (and (listp key) (eval key))
			 (and (numberp key) (= key cycle))
			 (and (stringp key) (search key id :test #'char-equal)))
		  do (return exprs))))
  (trace-cell-safe-for-trace-expr) ;; Avoid recursion when called from a trace expr
  )
(defun trace-cell-safe-for-trace-expr ()
  (when *cell-tracing-on*
    (loop for name-or-expr in *trace-cell-names-or-exprs* do
	    (if (listp name-or-expr)
		(let ((r (eval name-or-expr)))
		  (when r (format t "   ~s => ~s~%" name-or-expr r)))
		(format t "   ~a=~s ++ ~s~%" name-or-expr
			(<== name-or-expr)
			(ignore-errors ;; In case there's no number, or some other f'up in the eval
			  (cdr (getstack (<== name-or-expr) *stack-display-depth*))))))))

(defun getstack (head-name &optional depth)
  (cond ((or (and depth (zerop depth)) (zero? head-name)) nil)
	(t (let ((head-cell (<== head-name)))
	     (cons head-cell (getstack (cell-link head-cell) (and depth (1- depth))))))))

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

(defparameter *system-cells* '("H0" "H1" "H3" "H5"))
(defparameter *w-cells* (loop for w below 43 collect (format nil "W~a" w)))

(defparameter *all-system-cells* (append *system-cells* *w-cells*))

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
	do (format t "  ~s~%" cell)))

(defun ??? (&aux (*cell-tracing-on* t) (*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1" "W2")))
  (print *trace-instruction*) (terpri)
  (format t "H5=~a, H3(cycles)=~a~%" (cell "H5") (h3-cycles))
  (format t "*W24-Line-Buffer*=~s~%" *W24-Line-Buffer*)
  (trace-cell-safe-for-trace-expr)
  (backtrace!)
  )
(define-symbol-macro ?? (???))

;;; ===================================================================
;;; Loader (loads from files converted by tsv2lisp.py)

;;; FFF Note that the dumper puts multiple header lines in (:comments :type :name
;;; :sign :p :q :symb :link :comments.1 :id). Prob. need code to ignore them
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
			:p (decode-pq :p (nth (incf p) read-row) read-row)
			:q (decode-pq :q (nth p read-row) read-row)
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
			  (!! :load "** Execution start at ~s **~%" (cell-symb cell))
			  (save-cells (reverse cells) load-mode)
			  (setf cells nil)
			  (run (cell-symb cell) :adv-limit adv-limit))
			(if (and (zerop (cell-p cell)) (= (cell-q cell) 1))
			    (progn
			      (save-cells (reverse cells) load-mode) (setf cells nil)
			      (!! :load "Switching to DATA load mode.~%")
			      (setf load-mode :data))
			    (if (and (zerop (cell-p cell)) (zerop (cell-q cell)))
				(progn
				  (!! :load "Switching to CODE load mode.~%")
				  (save-cells (reverse cells) load-mode) (setf cells nil)
				  (setf load-mode :code))
				(!! :load "Ignoring: ~s~%" read-row)))))))
	  finally (save-cells (reverse cells) load-mode)
	  )))

(defun decode-pq (pq? val hint)
  (if (= 1 (length val))
      (let ((q (parse-integer val)))
	(format t "*** WARNING: PQ ~s (in ~s) is ambugious and intepreted as p=0, q=~a~%" val hint q)
	(case pq? (:p 0) (:q q)))
      (if (string-equal "" val) 0
	  (case pq? (:p (parse-integer (subseq val 0 1))) (:q (parse-integer (subseq val 1 2)))))))

(defparameter *symbol-col-accessors* `((cell-name . ,#'cell-name) (cell-symb . ,#'cell-symb) (cell-link . ,#'cell-link)))

(defun save-cells (cells load-mode)
  ;; Before doing anything else we massage data-type cards (load-mode :data) in
  ;; accord with the PQ.
  (when (eq load-mode :data)
    (loop for cell in cells
	  as p = (cell-p cell)
	  as q = (cell-q cell)
	  do (cond ((and (zerop p) (= q 1)) (setf (cell-link cell) (parse-integer (cell-link cell))))
		   ((and (= p 1) (= q 1)) (break "Floating point is not implemented: ~s" cell))
		   ((and (= p 2) (= q 1)) :noop) ;; Alpha -- just leave the symb as is
		   ((not (and (zerop p) (zerop q))) (break "Invalid PQ in ~s" cell)))))
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
				if (local-symbol-by-name? symbol)
				collect (cons symbol (format nil "~a-~a" top-name symbol)))))))
      (let ((missing-local-symbols (convert-local-symbols cells local-symbols.new-names)))
	(when (and missing-local-symbols (eq :code load-mode))
	  (setf cells (append cells (loop for missymb in missing-local-symbols
					  as new-name = (cdr (assoc missymb local-symbols.new-names :test #'string-equal))
					  do (format t "WARNING: Cell ~s is being added for missing local symbol ~s!~%" new-name missymb)
					  collect (make-cell! :name new-name :p 0 :q 0 :symb "0" :link "0"))))))
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
  (and (stringp name)
       (not (zerop (length name)))
       ;; ??? Might want to look at -9- or 9+ or other details ???
       (not (char-equal #\9 (aref name 0)))))

;;; WWW There are two completely different meanings of "local"
;;; symbol. The one implemented here is by name -- that is, any name
;;; that begins with "9" is local, and all others are global. The
;;; other sense is regarding a cell, where Q=2. This is implemented at
;;; te JFn level and is primarily used for marking graphs. See
;;; discussions with ChatBots in etc/ dir, as well as J74, J132, and J136
;;; https://chatgpt.com/share/6824cf31-9afc-8008-bd37-847e5b738ea1

(defun local-symbol-by-name? (name)
  (if (numberp name) nil
      (and (not (zerop (length name)))
	   (char-equal #\9 (aref name 0)))))

;;; This looks like it should be just (not (local-symbol-by-name? ...)) but
;;; there's this weirdness to make sure that the rest is all numbers.
;;; (This is barely ever used anyway. I think it's only used in line
;;; input.)

(defparameter *LT-Regional-Chars* "ABCDEFGIKLMNOPQRSTUVXYZ-*=,/+.()'")

(defun regional-symbol? (string)
  (and (find (aref string 0) *LT-Regional-Chars*)
       (or (= 1 (length string)) ;; case of single char symbols
	   (loop for p from 1 by 1
		 with lim = (1- (length string))
		 until (= p lim)
		 if (not (find (aref string p) "0123456789"))
		 do (return nil)
		 finally (return t)))))

(defun uniquify-list (l)
  (loop for i on l
	unless (member (car i) (cdr i) :test #'equal)
	collect (car i)))

(defun prettify-jexps-if-any (cell)
  (when (cell? cell)
    (let* ((symbexp (getf (gethash (cell-symb cell) *jfn-plists*) 'explanation))
	   (linkexp (getf (gethash (cell-link cell) *jfn-plists*) 'explanation)))
      (if (or symbexp linkexp) (format nil "~%               [~a | ~a]" (or  symbexp "") (or linkexp ""))
	  ""))))

(defun reset! ()
  (clrhash *symtab*) 
  ;;(initialize-system-cell-stacks)
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

(defun create-system-cells ()
  (loop for name in *all-system-cells*
	do (make-cell! :name name))
  (setf (cell "S") "S-is-null")
  )

;;; If any var becomes nil, there's something wrong!  (**EMPTY** is okay
;;; at the very end of the process.)

(defun check-for-overpopping ()
  (loop for name in *all-system-cells*
	as val = (gethash name *symtab*)
	if (null val)
	do (break "**** Oops! ~s is ~s, which is oughtn't be!" name val)))

;;; This is needed because of H0 memory leaks, probably from JFNS.
(defvar *stack-depth-limit* 100)

;;; Loaded code analysis:
;;; This throws an annoying warning and is a non-critical deugging tool
'(defun report-col-vals ()
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

(defvar *j74tbl* (make-hash-table :test #'equal))

(defvar *j15-mode* :clear-dl)

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

  (defj J1 ([0]) "EXECUTE (0)"
    ;;; The process, (0), is removed from H0, H0 is restored (this
    ;;; positions the process's inputs correctly), and the process is
    ;;; executed as if its name occurred in the instruction instead of
    ;;; J1.
    (poph0 1) ;; Pre-popping in this case should be safe.
    (ipl-eval [0]))

  (defj J2 ([0] [1]) "TEST (0) == (1)?" ;; The identity test
	;; is on the SYMBpart only; P and Q are ignored. [Also, in the
	;; case of alphabetics, trailing blanks or zeros are ignored.]
	;; Before we go anywhere else, the names could be equal or the
	;; name of one could be equal to the symbol of the other, in
	;; either direction. 
	(!! :jdeep (announce "   ~a=~a" [0] [1]))
	(if (ipl-string-equal [0] [1]) (H5+) (H5-))
	(poph0 2)
	;; ("p.10: "...it is understood from the definition of TEST
	;; that J2 will remove both (0) and (1) from HO.")
	)

  (defj J3 () "SET H5 -" (H5-))
  (defj J4 () "SET H5 +" (H5+))
  (defj J5 () "REVERSE H5" (if (string-equal "+" (H5)) (H5-) (H5+)))

  (defj J6 () "REVERSE (0) and (1)" 
	(let ((r1 (cell-symb (H0)))
	      (r2 (cell-symb (H0+))))
	  ;; !!! This is what you always have to do: Precompute your
	  ;; answers, then pop the inputs and push the outputs:
	  (poph0 2)
	  (ipush "H0" r1)
	  (ipush "H0" r2)))

  (defj J7 () "HALT, PROCEED ON GO"
    ;; The computer stops; if started again, it interprets the next
    ;; instruction in sequence. Aka....
    (break "J7: Processor halted ... use :C to continue."))

  (defj J8 () "RESTORE H0" (ipop "H0")) 

  (defj J9 () "ERASE CELL (0)"
	;; Maybe remhash the name from the symtab? FFF
	(!! :jdeep "             .....J9 just pops H0; We don't need to do our own GC.")
	(poph0 1))

  (defj J10 ([0] [1]) "FIND THE VALUE OF ATTRIBUTE (0) OF (1)" 
	;; If the symbol (0) is on the description list of list (1) as an
	;; attribute, then its value--i.e., the symbol following it--is output
	;; as (0) and H5 set + ; if not found, or if the description list
	;; doesn't exist, there is no output and H5 set - . (J10 is accomplished
	;; by a search and test of all attributes on the description list.) 
	(PopH0 2) ;; I think pre-popping is safe here because H0 won't ever be a list head.
	(!! :jdeep "             .....In J10 trying to find the value of ~s in ~s!" [0] [1])
	(!! :jdeep (announce "Find ~a in ~a" [0] [1]))
	(let* ((list-head (cell [1]))
	       (dlist-name (cell-symb list-head))
	       (target [0]))
	  (!! :jdeep "             .....In J10 list-head = ~s
                     dlist-name = ~s
                     target = ~s" list-head dlist-name target)
	  (if (zero? dlist-name)
	      (progn (!! :jdeep "             .....In J10 -- no dl, so we're done with H5-") (H5-))
	      (loop with dl-attribute-cell = (cell (cell-link (cell dlist-name)))
		    do ;; Note we're skipping the dl of the dl if any
		    ;; The first could be the last. This is sort of messy. FFF Unduplicate code %%%
		    (if (null dl-attribute-cell)
			(progn (!! :jdeep "             .....J10 failed (a) to find ~s." target)
			       (H5-) (return nil)))
		    (!! :jdeep "             .....In J10 dl-attribute-cell = ~s" dl-attribute-cell)
		    (if (ipl-string-equal target (cell-symb dl-attribute-cell))
			(let* ((cell (cell (cell-link dl-attribute-cell))))
			  (!! :jdeep "             .....J10 found ~s at ~s, returning ~s"
			      target dl-attribute-cell (cell-symb cell))
			  (H5+)
			  (ipush "H0" (cell-symb cell))
			  (return t))
			(let* ((next-att-link (cell-link dl-attribute-cell)))
			  (if (zero? next-att-link)
			      (progn
				(!! :jdeep "             .....J10 failed (b) to find ~s." target)
				(H5-) (return nil))
			      (setf dl-attribute-cell (cell (cell-link dl-attribute-cell))))))))))

  (defj J11 ([0] [1] [2]) "ASSIGN (1) AS THE VALUE OF ATTRIBUTE (0) OF (2)"
	;; After J11, the symbol (1) is on the description list of
	;; list (2) as the value of attribute (0). If (0) was already
	;; on the description list, the old value has been removed,
	;; and (1) has taken its place; if the old value was local, it
	;; has been erased as a list structure (J72). If (0) is a new
	;; attribute, it is placed at the front of the description
	;; list. [??? I'm not sure this lastcondition is implemented
	;; correctly???] J11 will create the description list (with a
	;; local name) if it does not exist (head of (2) empty). There
	;; is no output in HO. *** Def. needs to pop late !!!
	(let* ((att [0])
	       (val [1])
	       (list-head (cell [2]))
	       (maybe-dl-head (cell-symb list-head))
	       (dl-head (if (not (zero? maybe-dl-head))
			    (cell maybe-dl-head)
			    (progn (!! :jdeep "             .....In J11 no dlist yet for ~s so I'm creating one!" list-head)
				   (make-cell! :name (newsym) :p 0 :q 0 :symb "0" :link "0"))))
	       )
	  ;; Either get the DL for the list, or create one if it doesn't exist.
	  ;; (This is redundant if it was already there)
	  (setf (cell-symb list-head) (cell-name dl-head))
	  (J11-helper-add-to-dlist dl-head att val)
	  (!! :jdeep (pll [2]))
	  (PopH0 3)
	  ))

  (defj J14 ([0] [1]) "ERASE ATTRIBUTE (0) OF (1)"
	;; If the symbol (0) exists on the description list of list
	;; (1) as an attribute, both it and its value symbol are
	;; removed from the list. If either is local, it is erased as
	;; a list structure (J72). If (0) is not an attribute on the
	;; description list of (1), nothing is done. (In all cases the
	;; description list is left.)
	(let* ((head (<== [1]))
	       (dlname (cell-symb head)))
	  (if (zero? dlname) (break "J14 (ERASE ATTRIBUTE ~s OF ~s) called but ~s doesn't have a DList!" [0] [1] [1]))
	  (let ((dlhead (<== dlname)))
	    (setf (cell-link dlhead) (j14-helper [0] (cell-link dlhead)))))
	(poph0 2)
	)

  (defj J15 ([0]) "ERASE ALL ATTRIBUTES OF (0)"
	;; The description list of list (0) is erased as a list
	;; structure (J72), and the head of (0) is set empty. [???
	;; It's unclear here whether the DL is left and just cleared,
	;; or the DL pointer (symb) in the list-head is set to 0???
	;; The *j15-mode* is used to choose the one we want on a given
	;; run. So far it doesn't seem to matter.]
	(let ((lhead (<== [0])))
	  (!! :jdeep "             .....J15 clearing the dl of ~s (~s)" [0] lhead)
	  (case *J15-mode*
	    (:clear-dl
	     ;; This is the "Leave the DL but remove its contents"
	     (let ((dlhead (cell-symb lhead)))
	       (if (zero? dlhead)
		   (break "In  J15 trying to clear a DL that doesn't exist!")
		   (setf dlhead (<== dlhead) (cell-symb dlhead) "0" (cell-link dlhead) "0"))))
	    (:delete-dl
	     ;; This is the "Kill the DL at the list head" version:
	     (setf (cell-symb lhead) "0"))
	    (t (error "*J15-mode* must be either :clear-dl or :delete-dl"))
	  ))
	(poph0 1)
	)

  ;; ==================================================================
  ;; GENERATOR FUNCTIONALITY
  
  ;; Just as a reminder: (defvar *genstack* nil) (defstruct gentry fn wn :wnames +- gentag)

  (defj J17 (wn-symb fn) "GENERATOR SETUP" 
	(let ((gentag (gensym "GEN-")))
	  (!! :gentrace "    >>>>>>>>>> J17 [Gen Setup @~a] ~s ~s tag=~s >>>>>>>>>>"  (H3-cycles) wn-symb fn gentag)
	  (!! :gentrace (let ((*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1"))
			      (*cell-tracing-on* t))
			  (format t "Cell trace before:")
			  (trace-cells)))
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
			       :+- "+"
			       :gentag gentag)
		  *genstack*))
	  (!! :gentrace "             .....J17 *genstack* push: ~s" (car *genstack*))
	  (!! :gentrace "              *genstack*=~s"  *genstack*)
	  (!! :gentrace (let ((*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1"))
			      (*cell-tracing-on* t))
			  (format t "Cell trace after:")
			  (trace-cells)))
	  ))

  (defj J18 () "EXECUTE SUBPROCESS" 
	(!! :gentrace "         <><><><><> J18 [Gen Exec @~a] <><><><><>" (H3-cycles))
	(!! :gentrace (let ((*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1"))
			    (*cell-tracing-on* t))
			(format t "Cell trace before:")
			(trace-cells)))
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
	(!! :gentrace "             J18: entry:") (!! :gentrace (trace-cells))
	(let* ((gentry (first *genstack*))
	       (fn (gentry-fn gentry))
	       (wn (gentry-wn gentry))
	       (gentag (gentry-gentag gentry))
	       (wnames (gentry-wnames gentry))
	       ;; WVALS is the generator context, held by the lisp
	       ;; stack. (So we don't need a special stack for the
	       ;; generator context.)
	       (wvals (loop for wname in wnames
			    as wcell = (cell wname)
			    do (ipop wname)
			    collect wcell)))
	  (!! :gentrace "             J18 (tag=~s): collected wvals = ~s" gentag wvals)
	  (!! :gentrace "             J18: After Wn ipops:") (!! :gentrace (trace-cells))
	  (!! :gentrace "             J18: *genstack* = ~s" *genstack*)
	  (!! :gentrace "             .....J18 (fn=~s, wn=~s)" fn wn)
	  ;; This seems redundant with the one in J19, but that one is
	  ;; restoring the caller context, whereas this one is
	  ;; restoring the generator context.
	  ;; (J3n=restore-wn wn) !!! This was causing double poppage ~ 20250415
	  ;; We also temporarily pull the top of the genstack to reveal what's underneath in case there is a recursive generator in use. 
	  (let ((held-genstack-entry (pop *genstack*)))
	    (!! :gentrace "             .....J18 (tag=~s) holding ~s off the genstack..." gentag held-genstack-entry)
	    (!! :gentrace "             .....*genstack* is now: ~s" *genstack*)
	    (!! :gentrace "             .....J18 Executing ~s" fn)
	    (!! :gentrace "             J18: Just before IPL-EVAL:") (!! :gentrace (trace-cells))
	    (ipl-eval fn)
	    (!! :gentrace "             J18: Just after IPL-EVAL:") (!! :gentrace (trace-cells))
	    (!! :gentrace "             .....J18 ~s returned with H5=~a" fn (H5))
	    ;; Now we put it back
	    (push held-genstack-entry *genstack*))
	  (!! :gentrace "             J18: replaced wvals (should be the same as collected, above!)= ~s" wvals)
	  (loop for wname in wnames
		as wval in wvals
		do (ipush wname wval))
	  (!! :gentrace "             J18 (tag=~s): Just before return:" gentag) (!! :gentrace (trace-cells))
	  (setf (gentry-+- gentry) (H5))
	  (!! :gentrace (let ((*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1"))
			      (*cell-tracing-on* t))
			  (format t "Cell trace after:")
			  (trace-cells)))
	  ))

  (defj J19 () "GENERATOR CLEANUP"
	(!! :gentrace "    <<<<<<<<<< J19 [Gen Cleanup @~a] <<<<<<<<<<" (H3-cycles)) 
	(!! :gentrace (let ((*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1"))
			    (*cell-tracing-on* t))
			(format t "Cell trace before:")
			(trace-cells)))
	;; Has no input. Does three things: 1. Restores WO through
	;; Wn. 2. Restores all the cells of the hideout. 3. Places in
	;; H5. the recorded sign, which will be + if the generator went to
	;; completion (last subprocess communicated + ), and - if the
	;; generator was stopped (last subprocess communicated - ).
	(let* ((gentry (pop *genstack*))
	       (gentag (gentry-gentag gentry))
	       (wn (gentry-wn gentry))
	       (+- (gentry-+- gentry)))
	  (!! :gentrace "             .....J19 (tag=~s) popping gentry: ~s" gentag gentry)
	  ;; This seems redundant with the one in J18, but that one is
	  ;; restoring the generator context, whereas this one is
	  ;; restoring the caller context.
	  (J3n=restore-wn wn) 
	  (if (string-equal +- "+") (H5+)
	      (if (string-equal +- "-") (H5-)
		  (break "In J19 +- is ~s" +-))))
	  (!! :gentrace (let ((*trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1"))
			      (*cell-tracing-on* t))
			  (format t "Cell trace after:")
			  (trace-cells)))
	)

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

  (defj J60 ([0]) "LOCATE NEXT SYMBOL AFTER CELL (0)" 
	;; LOCATE NEXT SYMBOL AFTER CELL (0). (0) is the name of a
	;; cell. If a next cell exists (LINK of (0) not a termination
	;; symbol), then the output (0) is the name of the next cell,
	;; and H5 is set +. If LINK is a termination symbol, then the
	;; output (0) is the input (0), which is the name of the last
	;; cell on the list, and H5 is set -. No test is made to see
	;; that (0) is not a data term, and J60 will attempt to
	;; interpret a data term as a standard IPL cell.  !!! Must pop
	;; late (if at all) 
	(let* ((this-cell (cell [0]))
	       (link (cell-link this-cell)))
	  (!! :jdeep "             .....In J60, this-cell = ~s, link = ~s" this-cell link)
	  (if (zero? link)
	      ;; Notice that we don't pop on eol!
	      (progn (!! :jdeep "             .....In J60 no next cell!")
		     (H5-))
	      (progn (!! :jdeep "             .....In J60 next cell is ~s!" link)
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

(defj J62 ([0] [1]) "LOCATE (O) ON LIST (1)"
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
      (let* ((target [0])
	     (list-head (cell [1])))
	(!! :jdeep "             .....J62 trying to locate target:~s in linear list starting with cell ~s" target list-head)
	;; The H5 has to be set in the subfn bcs only it knows whether it succeeded.
	(let ((r (j62-helper-search-list-for-symb target list-head (cell-link list-head))))
	  (poph0 2) 
	  (ipush "H0" (cell-name r)))))

  (defj J63 (new-symbol list-cell-name) "INSERT (0) BEFORE SYMBOL IN (1)"
	;; (1) is assumed to name a cell in a list. A new cell is
	;; inserted in the list behind (1). The symbol in (1) is
	;; moved into the new cell, and (0) is put into (1). The end
	;; result is that (0) occurs in the list before the symbol
	;; that was originally in cell (1).
	(!! :jdeep "             .....******** In J64 WORRY ABOUT THE UNINTERPRETABLE TERMINATION CELL CASE!")
	(!! :jdeep "             .....=========================================================J64 trying to append ~s to ~s~%" new-symbol list-cell-name)
	(!! :jdeep "             .....Here are the lists before:")
	(let* ((list-cell (cell list-cell-name))
	       (new-cell-name (newsym))
	       (list-cell-symb (cell-symb list-cell))
	       (new-cell (make-cell! :name new-cell-name :symb list-cell-symbol :link (cell-link list-cell))))
	  (declare (ignore new-cell))
	  (setf (cell-symb list-cell) new-symbol
		(cell-link list-cell) new-cell-name))
	(!! :jdeep "             .....*********************************************************")
	(!! :jdeep "             .....Here is the target list, after:")
	(!! :jdeep (pl list-cell-name))
	(!! :jdeep "             .....=========================================================")
	(poph0 2)
	)

  ;; This is probably the most important function of all, and if hard
  ;; to get right because it depends upon subtlties of locality and
  ;; such.

  (defj J64 (new-symbol list-cell-name) "INSERT (0) AFTER SYMBOL IN (1)"
	;; (format t "~%~%***************** (J64 :Insert ~s :In ~s) *****************!~%~%" new-symbol list-cell-name)
	;; (format t "~%~%--------------------------~%~%")
	;; (pl "L11") 
	;; (format t "~%~%--------------------------~%~%")
	;; Identical with J63, except the symbol in (1) is left in
	;; (1), and (0) is put into the new cell, thus occurring after
	;; the symbol in (1). (If (1) is a private termination symbol,
	;; (0) is put in cell (1), which agrees with the definition of
	;; insert after.) [WWW???!!! I dunno WTF this is talking
	;; about! And it's prob. gonna break at list ends because
	;; ... see above!] There seems to be a screw case here. If
	;; we're handed a cell that is x|0|0 we don't know if that's a
	;; list header or a "private termination symbol" because we
	;; don't have the concept of privacy other than the names. If
	;; we do this wrong, it's gonna put the new thing into the DL
	;; of this list, which is decidedly NOT right. So, we
	;; heuristically assume that x|0|0 is a list header, and in
	;; this case add a new cell to the tail anyway, but flag an
	;; alert..
	(!! :jdeep "             .....=========================================================J64 trying to append ~s to ~s~%" new-symbol list-cell-name)
	(!! :jdeep "             .....Here are the lists before:")
	(!! :jdeep (pl new-symbol) (pl list-cell-name))
	(let* ((list-cell (cell list-cell-name))
	       (list-cell-symb (cell-symb list-cell))
	       (list-cell-link (cell-link list-cell))
	       (new-cell-name (newsym))
	       (new-cell (make-cell! :name new-cell-name
				     :symb new-symbol
				     :link list-cell-link)))
	  ;;; If the cell we've been handed is heuristically an empty
	  ;;; list header, we soft flag this and add the new cell to
	  ;;; the end.
	  (when (and (zero? list-cell-symb) (zero? list-cell-link))
	    (!! :alert "             .....J64 was handed what is assumed to be a list header: ~s!" list-cell))
	  ;; So, all we need to do now is to link the new cell to the
	  ;; given one, since the list cell link was already added
	  ;; (representing the rest of the list) when the new cell was
	  ;; created.
	  (setf (cell-link list-cell) new-cell-name)
	  ;; (format t "~%~%--------------------------~%~%")
	  ;; (pl list-cell-name) 
	  ;; (format t "~%~%--------------------------~%~%")
	  ;; (pl "L11") 
	  ;; (format t "~%~%--------------------------~%~%")
	  )
	(!! :jdeep "             .....*********************************************************")
	(!! :jdeep "             .....Here is the target list, after:")
	(!! :jdeep (pl list-cell-name))
	(!! :jdeep "             .....=========================================================")
	(poph0 2)
	)

  ;; WWW If this tries to work with numeric data there's gonna be a
  ;; problem bcs PQ will be wrong.
  (defj J65 ([0] [1]) "INSERT (0) AT END OF LIST (1)"
	(!! :jdeep (announce "~a =++ ~a" [0] [1]))
	;; Identical to J66 except that it always inserts at the end
	;; of the list.
	(!! :jdeep "             .....=========================================================J65 trying to append ~s to ~s~%" [0] [1])
	(!! :jdeep "             .....Here are the lists before:")
	(!! :jdeep (pl [0]) (pl [1]))
	(loop with list-cell = (cell [1])
	      with symb = [0]
	      with new-cell = (make-cell! :name (newsym) :symb symb :link "0")
	      do
	      (cond ((zero? (cell-link list-cell))
		     (!! :jdeep "             .....J65 hit end, adding ~s to the list at ~s!" new-cell list-cell)
		     (setf (cell-link list-cell) (cell-name new-cell))
		     (return t)))
	      ;; Move to next cell if nothing above returned out
	      (setf list-cell (cell (cell-link list-cell))))
	(!! :jdeep "             .....*********************************************************")
	(!! :jdeep "             .....Here is the target list, after:")
	(!! :jdeep (pl [1]))
	(!! :jdeep "             .....=========================================================")
	(PopH0 2)
	)

  (defj J66 ([0] [1]) "INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT" 
	;; J66 INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT. A
	;; search of list (1) is made. against (0) (starting with the
	;; cell after cell (1) . If (0) is found, J66 does nothing
	;; further. If (0) is not found, it is inserted at the end of
	;; the list, as in J65. [Nb. This can't do anything sensible
	;; with a branching list!]
	(let ((target [0]))
	  (!! :jdeep "             .....J66 trying to insert ~s in ~s" target [1])
	  (loop with list-cell = (<=! [1])
		as link = (cell-link list-cell)
		do
		(cond ((string-equal (cell-symb list-cell) target)
		       (!! :jdeep "             .....J66 found ~s in the list already. No action!" target)
		       (PopH0 2) (return nil))
		      ((zero? link)
		       (!! :jdeep "             .....J66 hit end, adding ~s to the end of the list!" target)
		       (setf (cell-link list-cell)
			     (cell-name (make-cell! :name (newsym) :symb target :link "0")))
		       (PopH0 2) (return t)))
		;; Move to next cell if nothing above returned out
		(setf list-cell (cell (cell-link list-cell))))))
 
  (defj J68 ([0]) "DELETE SYMBOL IN CELL (0)"
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
	(let* ((this-cell (<== [0])) ;; was <=!
	       (next-cell-name (cell-link this-cell)))
	  (if (zero? next-cell-name)
	      (progn (!! "J68 hit the end of the list.")
		     (H5-))
	      ;; Here's the complex work. Ugh!
	      (let* ((next-cell (cell next-cell-name)))
		(!! "J68 Moving symbol in ~s to ~s and deleting ~s."
		    next-cell this-cell next-cell)
		(setf (cell-symb this-cell) (cell-symb next-cell)
		      (cell-link this-cell) (cell-link next-cell)))))
	(poph0 1)
	)

  (defj J71 ([0]) "ERASE LIST (0)"
	(declare (ignore [0]))
	;; (0) is assumed to name a list. All cells of the list--both
	;; head and list cells--are returned to available
	;; space. (Nothing else is returned, not even the description
	;; list of (0), if it exists.) There is no out-put in HO. If
	;; (0) names a list cell, the cell linking to it will be
	;; linking to available space after J71, a dangerous but not
	;; always fatal situation.
	(poph0 1))

  (defj J72 ([0]) "ERASE LIST STRUCTURE (0)"
	(declare (ignore [0]))
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

  ;; =======================
  ;; IPL-V List Copying Functions (Updated to Handle Q=2 Local Symbols)

  ;; In IPL-V, the Q=2 designation used to mark a symbol as "local" does not modify the symbol itself
  ;; or the cell it names. Instead, it is a property of the IPL word (cell) that contains the symbol in
  ;; its SYMB field. When the Q field of such a word is set to 2, it signals to the loader or copier
  ;; (e.g., during J74) that the symbol should be treated as local—meaning it will be replaced with a
  ;; newly generated, unique name. This ensures the symbol is localized to the copied context and avoids
  ;; naming collisions. This behavior is described explicitly on:
  ;;   - Page 200, under J136: "The output (0) is the input (0) with Q = 2..."
  ;;   - Page 148: "If the SYMB field of a word is marked with Q=2, the loader recognizes it as a local symbol."
  ;;   - Page 29: "To create a local symbol... set Q=2 in the cell in which the name appears."

  (defj J73 ([0]) "(Shallow) Copy list [186]"
	;; COPYLIST (0). The output (0) names a new list, with the
	;; identical symbols in the cells as are in the corresponding
	;; cells of list (0), including the head. If (0) is the name
	;; of a list cell, rather that [sic: than] a head, the output
	;; (0) will be a copy of the remainder of the list from (0)
	;; on. (Nothing else is copied, not even the description list
	;; of (0), if it exists.)  The name is local if the input (0)
	;; is local; otherwise, it is internal.  [This isn't in the
	;; manual, but for sometimes this is handed a 0 -- e.g., we're
	;; trying to copy the DL of a list but there's no DL. In this
	;; case we flag it and create a null list, hoping that the
	;; caller might think it's what it's looking for. FFF ??? It's
	;; actually pretty likely that a bug in my code is sending
	;; these 0s, and this hack is covering up for that.]
	(!! :jdeep "             .....J73 is shallow copying list: ~s" [0])
	(!! :jdeep "                  Incoming list:")
	(!! :jdeep (pl [0]))
	(let* ((new-head
		(if (zero? [0])
		    (let* ((new-cell (make-cell! :p 0 :q 0 :symb "0" :link "0")))
		      (!! :alerts "            .....j73 passed a '0' is creating a blank list cell: ~s" new-cell)
		      (cell-name new-cell))
		    (J73-shallow-copy-ipl-list [0]))))
	  (poph0 1)
	  (!! :jdeep "                  Incoming list (to check for damage!):")
	  (!! :jdeep (pl [0]))
	  (!! :jdeep "                  Copy:")
	  (!! :jdeep (pl new-head))
	  (ipush "H0" new-head)))

  (defj J74 ([0]) "(Deep) Copy List Structure [186]"
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
	(!! :jdeep "             .....J74 is deep copying list: ~s" [0])
	(!! :jdeep "                  Incoming list:")
	(!! :jdeep (pl [0]))
	(clrhash *j74tbl*)
	(let* ((new-head
		(if (zero? [0])
		    (let* ((new-cell (make-cell! :p 0 :q 0 :symb "0" :link "0")))
		      (!! :alerts "            .....j73 passed a '0' is creating a blank list cell: ~s" new-cell)
		      (cell-name new-cell))
		    (J74-deep-copy-ipl-list [0]))))
	  (poph0 1)
	  (!! :jdeep "                  Incoming list (to check for damage!):")
	  (!! :jdeep (pl [0]))
	  (!! :jdeep "                  Copy:")
	  (!! :jdeep (pl new-head))
	  (ipush "H0" new-head)))

  (defj J75 ([0]) "DIVIDE LIST AFTER LOCATION (0)"
	;; (0) is assumed to be the name of a cell on a list. A
	;; termination symbol is put for LINK of (0), thus making (0)
	;; the last cell on the list. The output (0) names the
	;; remainder list: a new blank head followed by the string of
	;; list cells that occurred after cell (0).
	(!! :jdeep "             .....J75 is dividing a list at: ~s" [0])
	(let* ((split-cell (<== [0]))
	       (new-head (make-cell! :name (newsym) :link (cell-link split-cell))))
	  (setf (cell-link split-cell) "0")
	  (!! :jdeep "             .....J75 splitting a list: New tail: ~s, New head (H0): ~s" split-cell new-head)
	  (let* ((r (cell-name new-head)))
	    (poph0 1)
	    (ipush "H0" r))))

  (defj J76 ([0] [1]) "INSERT LIST (O) AFTER CELL (1) AND LOCATE LAST SYMBOL"
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
	(!! :jdeep "             .....J76 is inserting ~a after ~a" [0] [1])
	(let* ((l0 (<== [0]))
	       (c1 (<== [1]))
	       (c1link (cell-link c1))
	       (last-cell-in-l0 (last-cell-of-linear-list l0)))
	  (cond ((zero? (cell-link l0))
		 (poph0 2)
		 (ipush "H0" (cell-name c1))
		 (H5-))
		(t (setf (cell-link c1) (cell-link l0))
		   (setf (cell-link last-cell-in-l0) c1link)
		   (poph0 2)
		   (ipush "H0" (Cell-name last-cell-in-l0))))))

  (defj J78 ([0]) "TEST IF LIST (0) IS NOT EMPTY"
	;; H5 is set - if LINK of (0) is a termination symbol, and set + if not.
	(if (zero? (cell-link (cell [0]))) (H5-) (H5+))
	(poph0 1)
	)

  (defj J79 ([0]) "TEST IF CELL (0) IS NOTEMPTY"
	;; H5 is set - if SYMB of (0) is 0, and set + otherwise. (Q of
	;; (0) is ignored; thus, both cells holding internal zero and
	;; termination cells give H5-). [??? It looks like this should
	;; be getting the name of a cell, but in the one call that
	;; it's used in LT - M054R130 - H0={...|0|0|0}, so ...hmmmm?]
	(if (zero? [0]) (format t "WARNING: @~a J79 IS PROBABLY GETTING BAD INPUT: ~s~%" (h3-cycles) [0]))
	(if (or (zero? [0]) (zero? (cell-symb (cell [0])))) (H5-) (H5+))
	(poph0 1))

  ;; J8n: FIND THE nth SYMBOL ON LIST (0) 0 <== n <== 9. (Ten routines: J80-J89)
  ;; Set H5 + if the nth symbol exists, - if not. Assume list (0) describable,
  ;; so that J81 finds symbol in first list cell, etc. J80 finds symbol in head;
  ;; and sets H5- if (0) is a termination symbol. 

  (defj J80 ([0]) "FIND THE HEAD SYMBOL OF (0)"
	(h5+)
	(if (zero? [0])
	    (progn (H5-) (poph0 1))
	    (let* ((r (cell-symb (cell [0]))))
	      (if (zero? r)
		  (progn (H5-) (poph0 1))
		  (progn (poph0 1) (ipush "H0" r))))))

;;; FIND THE NTH SYMBOL ON LIST (0) Ten routines, J80-J89. Set H5+ if
;;; the Nth symbol exists, - if not. Assume list (0) is de-scribable,
;;; so that J81 finds symbol in first list cell, etc. J80 finds
;;; symbol in head; and sets H5- if (0) is a termination symbol.

  (defj J81 ([0]) "FIND THE 1st (non-head) SYMBOL OF (0)"
	(j8n-helper (cell-link (cell [0])) 1))

  (defj J82 ([0]) "FIND THE 2nd (non-head0 SYMBOL OF (0)"
	(j8n-helper (cell-link (cell [0])) 2))
	      
  ;; J9n CREATE A LIST OF THE n SYMBOLS (n-1), (n-2), ..., (1), (0), 0
  ;; < n < 9. The order is (n-1) first, (n-2) second, ..., (0)
  ;; last. The output (0) is the name (internal) of the new list; it
  ;; is describable. J90 creates an empty list (also used to create
  ;; empty storage cells, and empty data terms).

  (defj J90 () "Create a blank cell on H0"  
	;; J90: Get a cell from the available space list, H2, and leave its name in HO.
	;; J90 creates an empty list (also used to create empty storage cells, and empty data terms).
	;; The output (0) is the name a the new list.
	(let* ((name (newsym))
	       (cell (make-cell! :name name :symb "0" :link "0")))
	  (!! :jdeep "            .....J90 creating blank list cell: ~s" cell)
	  (ipush "H0" name)))

  (defj J91 () "Create a list of 1 entry" (J9n-helper 1))
  (defj J92 () "Create a list of 2 entries" (J9n-helper 2))
  (defj J93 () "Create a list of 3 entries" (J9n-helper 3))

  (defj J100 ([0] [1]) "GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0)" 
	;; J100 GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0). The subprocess
	;; named (0) is performed successively with each of the symbols of list named
	;; (1) as input. The order is the order on the list, starting with the first
	;; list cell. H5 is always set + at the start of the subprocess. J100 will
	;; move in list (1) if it is on auxiliary. [This assumes a linear list.]
	(!! :jdeep "             .....J100 GENERATE SYMBOLS FROM LIST ~s FOR SUBPROCESS ~s" [1] [0])
	(loop with cell-name = (cell-link (cell [1]))
	      with cell = nil
	      with exec-symb = [0]
	      with inputs-popped = nil
	      until (zero? cell-name)
	      do 
	      (!! :jdeep "             .....J100: cell-name=~s, cell=~s" cell-name cell)
	      (setf cell (cell cell-name))
	      ;; Setup: arg->H0 and H5=+
	      (let* ((r (cell-symb cell)))
		;; This only pops the 2 inputs on the first call-down!
		;; Be afraid...be very afraid!  See! I told you to be
		;; afraid! If this call doesn't happen, the args get
		;; left on the stack .. see FINALLY fix, below.
		(unless inputs-popped (poph0 2) (setf inputs-popped t))
		(ipush "H0" r))
	      (H5+)
	      (!! :jdeep "             .....J100: Exec'ing ~s on ~s" exec-symb (cell-symb (h0)))
	      (ipl-eval exec-symb)
	      (setf cell-name (cell-link cell))
	      (!! :jdeep "             .....J100 returned, H5=~s, next cell-name=~s" (H5) cell-name)
	      finally (unless inputs-popped (poph0 2)) ;; In case NOTHING is called still need to do the pops!!
	      ))

  (defj J110 ([0] [1] [2]) "(1) + (2) = (O)" 
	;; The number (0) is set equal to the algebraic difference between numbers
	;; (1) and (2). The output (0) is the input (0). [So the stack management is a bit messy.]
	(let* ((n1 (numget [1]))
	       (n2 (numget [2]))
	       (r (+ n1 n2)))
	  (!! :jdeep "             .....J110: ~a + ~a = ~a" n1 n2 r)
	  (poph0 3)
	  (ipush "H0" [0])
	  (numset [0] r)))

  (defj J111 ([0] [1] [2]) "(1) - (2) -> (O)." 
	;; The number (0) is set equal to the algebraic difference between numbers
	;; (1) and (2). The output (0) is the input (0). [So the stack management is a bit messy.]
	(let* ((n1 (numget [1]))
	       (n2 (numget [2]))
	       (r (- n1 n2)))
	  (!! :jdeep "             .....J111: ~a - ~a = ~a" n1 n2 r)
	  (poph0 3)
	  (ipush "H0" [0])
	  (numset [0] r)))

  (defj J114 ([0] [1]) "TEST IF (0) = (1)" 
	(if (= (numget [0]) (numget [1])) (h5+) (h5-))
	(poph0 2))

  (defj J115 ([0] [1]) "TEST IF (0) > (1)" 
	(if (> (numget [0]) (numget [1])) (h5+) (h5-))
	(poph0 2))

  (defj J116 ([0] [1]) "TEST IF (0) < (1)"
	(if (< (numget [0]) (numget [1])) (h5+) (h5-))
	(poph0 2))

  (defj J117 ([0]) "TEST IF (0) = 0." 
	(let* ((n (numget [0])))
	  (!! :jdeep "             .....J117: Testing if ~s (~s: ~s) = 0?" [0] (<=! [0]) n)
	  (if (zerop n) (H5+) (H5-)))
	(poph0 1))

  (defj J120 ([0]) "COPY (0)"
	;; COPY (0). The output (0) names a new cell containing the
	;; identical contents to (0). The name is local if the input
	;; (0) is local; otherwise, it is internal.
	;; (No pop bcs H0 is replaced -- Maybe pop and push?)
	;; (?? Can this be replaced with FORCE-REPLACE ??)
	(let* ((old-cell (cell [0]))
	       (new-cell-name (newsym)))
	  (make-cell!
	   :name new-cell-name
	   :p (cell-p old-cell)
	   :q (cell-q old-cell)
	   :symb (cell-symb old-cell)
	   :link (cell-link old-cell))
	  (setf (cell-symb (H0)) new-cell-name)))
  
  (defj J121 (to from) "SET (O) IDENTICAL TO (1)"
	;; The contents of the cell named (1) is places in the cell
	;; (0). The output (0) is the input (0). [????]
	(setf (cell-link (cell to)) (cell-link (cell from)))
	(poph0 2)
	(ipush "H0" to))

  (defj J124 ([0]) "CLEAR (0)" 
	;; The number (0) is set to be 0. If the cell is not a data
	;; term, it is made an integer data term=0. If a number, its
	;; type, integer, or floating point, is unaffected. It is left
	;; as the output (0).  (NO POP!?!?)
	(!! :jdeep "             .....J124: Clear (H0): ~s" [0])
	(numset [0] 0))

;************************************* 

  (defj J125 ([0]) "TALLY 1 IN (0)" 
	;; An integer 1 is added to the number (0). The type of the
	;; result is the same as the type of (0). It is left as the
	;; output (0). [NNN: If there is no value in (0) this assumes
	;; zero and set the number to 1"] Nb. NO POP! "It is left as
	;; the output (0)." !!
	(let* ((curval (numget [0])))
	  (!! :jdeep "             .....J125: Tally (0) currently: ~s" [0])
	  (numset [0]
		  (if (not (numberp curval))
		      (progn (!! :jdeep "             .....Warning! J125 was sent a non-number: ~s, setting result to 1" curval) 1)
		      (1+ curval)))))

  (defj J126 ([0]) "COUNT LIST (0)"
	;; The output (0) is an integer data term, whose value is the
	;; number of list cells in list (0) (i.e., it doesn't count
	;; the head). If (0) = H2, J126 will count the available space
	;; list. This is the only place where H2 can be used safely by
	;; the programmer. [Nb. H2 is not passed to COUNT LIST in LT]
	(let* ((count-cell (make-cell! :name (newsym) :p 1 :q 2 :link 0))
	       (count-cell-name (cell-name count-cell))
	       (list-head (cell [0]))
	       (next-cell-name (cell-link list-head))
	       (count 0))
	  (!! :jdeep "             J126 counting ~a:" [0])
	  (!! :jdeep (pll (cell [0])))
	  (loop until (zero? next-cell-name)
		do (incf count)
		(setf next-cell-name (cell-link (cell next-cell-name)))
		finally (progn (poph0 1)
			       (numset count-cell-name count)
			       (!! :jdeep "             J126 result is ~s:" count-cell)
			       (ipush "H0" count-cell-name))
		)))

  ;; The concept of a local symbol is a little messed up in my
  ;; emulator. In the original IPL machine these symbols get cells
  ;; that get marked local or global using Q=2 or 0 -- I think. Maybe
  ;; I should do that, but I don't, really. What I do it use the
  ;; symbol's name to tell if it's local if it has a dash in it. This
  ;; precludes allowing global symbols with dashes, but that doesn't
  ;; worrry my much ... for now, anyway. Some of the IPL-V code I've
  ;; come across does have -s in it...and 9- might be a better test,
  ;; or I could do The Right Thing. ... Hahahahahah!

  (defj J130 ([0]) "TEST IF (O) IS REGIONAL SYMBOL"
	(if (find #\- [0]) (H5-) (H5+))
	(poph0 1))

  (defj J132 ([0]) "TEST IF (O) IS LOCAL SYMBOL"
	(if (find #\- [0]) (H5+) (H5-))
	(poph0 1))

  (defj J133 (l) "TEST IF LIST (0) HAS BEEN MARKED PROCESSED"
	;; Tests if P = 1 (and Q != 1 or 5) in the cell whose name is
	;; (0). It will only be 1 if list (0) has been preserved and P
	;; = 1 put in its head by J137. This means list (0) has been
	;; marked processed. 
	(poph0 1)
	(let* ((l (<== l))
	       (p (cell-p l))
	       (q (cell-q l)))
	  (if (and (= p 1) (member q '(0 2 3 4 6 7)))
	      (H5+) (H5-))))

  (defj J136 (H0) "MAKE SYMBOL (O) LOCAL."
	;; !!! SEE NOTES AT J73/74 !!!
	;; The output (0) is the input (0) with Q = 2. Since all
	;; copies of this symbol carry along the Q value, if a symbol
	;; is made local when created, it will be local in all its
	;; occurrences. [I have no idea what his last sentence means,
	;; but I actually think that this doesn't matter.]  (No pop
	;; bcs output is the input). 20250514: Experiments show that
	;; this is always called on a symb that's already local (as in
	;; it starts with 9-) so although this does set the Q of the
	;; target cell to 2, it probably doesn't actually do anything
	;; useful. Note long complex converstions with Claude and
	;; ChatGPT about this in notes.txt.]
	(let ((cell (<== H0)))
	  (setf (cell-q cell) 2)))

  (defj J137 ([0]) "MARK LIST (0) PROCESSED"
	;; List (0) is preserved, its [new] head made empty (Q =
	;; 4, SYMB = 0), and P set to be 1. Restoring (0) will return
	;; (0) to its initial state. This will work even with data
	;; terms. The output (0) is the input (0).
	(let* ((head-cell (<== [0]))
	       (current-first-cell-name (cell-link head-cell))
	       (current-first-cell (<== current-first-cell-name))
	       (new-first-cell-name (newsym))
	       (new-first-cell (make-cell! :name new-first-cell-name :p 1 :q 4 :symb "0" :link current-first-cell-name))
	       )
	  (setf (cell-link head-cell) new-first-cell-name)
	  (!! :jdeep "   .....J137 created new cell ~s in list: ~s" new-first-cell head-cell)
	  (!! :jdeep (pl [0]))
	  ))


  (defj J137 (l) "MARK LIST (0) PROCESSED"
	;; List (0) is preserved [ipushed], its [new] head made empty (Q =
	;; 4, SYMB = 0), and P set to be 1. Restoring (0) will return
	;; (0) to its initial state. This will work even with data
	;; terms. The output (0) is the input (0).
	;(poph0 1)
	(ipush l) ;; This will leave a copy in the main symtab.
	(let ((newmain (cell l))) ;; This should be the NEW copy of the pushed head.
	  ;; Now we mark the new main cell as indicated.
	  (setf (cell-q newmain) 4 (cell-symb newmain) "0")
	  ))

  (defj J138 ([0]) "J138 MAKE SYMBOL (O) INTERNAL"
	;; The output (0) is the input (0) with Q = 4. Best considered
	;; as "unmake local symbol." [Whatever the f any of that
	;; means! This is one of those confusing ones where it seems
	;; to indicate that the symbol includes the PQ.]
	(setf (cell-q (<== [0])) 4))

  (defj J147 ([0]) "MARK ROUTINE (O) TO TRACE"
	;; FFF Maybe actually turn tracing on! :-)
	(declare (ignore [0]))
	(poph0 1))

  (defj J148 () "MARK ROUTINE (0) TO PROPAGATE TRACE." 	;; Pop????
	;; Identical to J147, except uses Q = 4.
	(!! :jdeep "             .....J148 (MARK ROUTINE (0) TO PROPAGATE TRACE.) is a noop."))

  ;; Input and output are completely kludged, and unlike in original IPL. Partly
  ;; this is required because we don't have the same sort of physical
  ;; environment. There are tapes, and so on. But also, partly it's for
  ;; kludge-convenience. For example, there is exactly one 80 column
  ;; input/output buffer and it's used for all input and output.

  (defj J151 ([0]) "Print list (0)" 
	(print-linear-list [0])
	(PopH0 1)
	)

  (defj J152 ([0]) "PRINT SYMBOL (0)" 
	;; Pop after!!
	(PopH0 1)
	(pretty-print-cell (cell [0])))

  (defj J154 () "Clear print line"
	;; Clear Print Line CLEAR PRINT LINE. Print line 1W24 is cleared and the
	;; current entry column, 1W25, is set equal to the left margin, 1W21 [always 1 at the moment].
	(setf *W24-Line-Buffer* (blank80))
	(W25-set 0))

  (defj J155 () "Print line"
	(format t ":::::::::::::::::::::::::::::::: ~a~%" (hack-output!! *W24-Line-Buffer*))
	)

  (defj J156 ([0]) "ENTER SYMBOL (0) LEFT-JUSTIFIED"
	;; Symbol (0) is entered in the current print line with its
	;; leftmost character in print position 1W25, 1W25 is advanced
	;; to the next column after those in which (0) is entered, and
	;; H5 is set + . If (0) exceeds the remaining space, no entry
	;; is made and H5 is set - .
	(PopH0 1)
	(let* ((s [0]) ;;(cell-symb (<=! [0])))
	       (l (length s))
	       (p (W25-get)))
	  (!! :io "             .....J156 trying to add ~s at pos ~a in print butter." s p)
	  (if (<= (+ p l) 80)
	      (loop for m from p by 1
		    as c across s
		    do (setf (aref *W24-Line-Buffer* m) c)
		    finally (progn (W25-set (+ l p))
				   (H5+)))
	      (H5-)))
	(!! :io "             .....Print buffer is now:~s~%" *W24-Line-Buffer*)
	)

  (defj J157 (a0) "ENTER DATA TERM (0) LEFT-JUSTIFIED [216]"
	;; Data term (0) is entered in the current print line with its
	;; leftmost character in print position 1W25, 1W25 is
	;; advanced, and H5 is set + . If (0) exceeds the remaining
	;; space, no entry is made and H5 is set - .
	(poph0 1)
	(block J157A
	  (let* ((s (cell-symb (cell a0)))
		 (l (length s))
		 (p (W25-get)))
	    (!! :io "             .....J157 called on ~s, string: ~s (w25=~a)" a0 s p)
	    (when (> (+ l p) 80) (H5-) (return-from J157A nil)) ;; (Sadly, J157 isn't a DEFUN'ed block)
	    (loop for c across s
		  as i from p by 1
		  do (setf (aref *W24-Line-Buffer* i) c))
	    (W25-set (+ l p))
	    (H5+)
	    (!! :io "             .....Print buffer is now:~s (w25=~a)~%" *W24-Line-Buffer* (W25-get))
	    )))

  (defj J160 (col) "TAB TO COL (0)"
	(poph0 1)
	(let ((col (numget col)))
	  (!! :io "             .....Tabbing to ~a" col)
	  (W25-set col)))

  (defj J161 (a0) "INCREMENT COLUMN BY (0)"
	;; (0) is taken as the name of an integer data term. Current
	;; entry column, 1W25, is set equal to 1W25 + (0).
	(poph0 1)
	(let ((r (+ (cell-link (cell a0)) (W25-get))))
	  (!! :io "             .....New col is ~a" r)
	  (W25-set r)))
  
  (defj J166 () "SAVE ON UNIT (O) FOR RESTART"
	(PopH0 0)
	(!! :jdeep "             .....Yeah, I'm gonna pass on implementing J166 (Save for restart)!")
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
	  (!! :io "             .....J180 Read: ~s" line)
	  (H5+)
	  (if line (scan-input-into-*W24-Line-Buffer* line) (H5-))
	  (W25-set 0)
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
	(let* ((w25p (w25-get))
	       (w30n (numget (cell-symb (cell "W30"))))
	       (start (1- w25p))
	       (end (+ start w30n))
	       (string (subseq *W24-Line-Buffer* start end)))
	  ;; Note that, unlike J182, here "All non-numerical
	  ;; characters except in the first column are ignored." So we
	  ;; need a special scraping step to carry this out.
	  (setf string (j181-helper-remove-non-numeric-except-first string))
	  (!! :jdeep "             .....J181 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a]" string start end *W24-Line-Buffer* w25p w30n)
	  (W25-set (+ (W25-get) w30n))
	  (if (regional-symbol? string)
	      (progn
		(!! :jdeep "             .....J181 decided that ~s IS a regional symbol, so we're installing it." string)
		(make-cell! :name string :symb "0" :link "0")
		(ipush "H0" string)
		(H5+))
	      (progn
		(!! :jdeep "             .....J181 decided that ~s is NOT a regional symbol." string)
		(ipush "H0" string)
		(H5-)))))

  (defj J182 ([0]) "INPUT LINE DATATERM (0)" 
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
	;; octal integer data terms, non-numerical characters are
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
	  (setf (cell-symb (cell [0])) string) 
	  (W25-set (+ (W25-get) w30n))
	  (!! :jdeep "             .....J182 extracted ~s (~a-~a in ~s) [w25=~a, w30=~a] and jammed it into ~s"
	      string start end *W24-Line-Buffer* w25p w30n [0])
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

  (defj J183 ([0]) "SET (0) TO NEXT BLANK"
	;; 183/4 the term indicated by (0) is updated, so NO POP H0!
	(J183/4-Scanner [0] :blank))
 
  (defj J184 ([0]) "SET (0) TO NEXT NON-BLANK"
	;; Same as J183, except scans for any non-blank character.
	;; 183/4 the term indicated by (0) is updated, so NO POP H0!
	(J183/4-Scanner [0] :non-blank))

  (defj J186 () "INPUT LINE CHARACTER"
	;; The character in column 1W25 of line 1W24 is input to HO,
	;; H5 is set +. If the character is numerical, that internal
	;; symbol is input; if the character is non-numerical, the
	;; zeroth symbol in the region designated by that character is
	;; input; i.e., A->AO, 3->3. If the character is a blank,
	;; there is no input and H5 is set - In either case, 1W25 is
	;; not advanced.
	(let* ((c (aref *W24-Line-Buffer* (1- (w25-get)))))
	  (!! :jdeep "             .....J186 read ~s" c)
	  (if (char-equal #\space c)
	      (H5-)
	      (progn
		(ipush "H0" (format nil (if (numchar? c) "~c" "~c0") c))
		(H5+)))))

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

;;; There's this whole mess about zeros following certain characters
;;; because they are symbols and such like. This cleans up these
;;; hacks. FFF figure out what's supposed suppose to happen to avoid
;;; this mess.

(defun hack-output!! (s)
  (loop with r = (blanks 80)
	with l = (length s)
	as p below l
	as o below l
	as c across s
	with skip1 = nil
	do
	(if skip1
	    (setf skip1 nil o (1- o))
	    (progn 
	      (setf (aref r o) c)
	      (if (and (member c '(#\( #\)) :test #'char-equal)
		       (char-equal #\0 (aref s (1+ p))))
		  (setf skip1 t))))
	finally (return r)))

;;; Used to pop the inputs of JFns. You need to be VERY CAREFUL about
;;; when in the JFn you do pop the args bcs the JFn may want to use
;;; H0! 

(defun PopH0 (n) (dotimes (i (abs n)) (ipop "H0")))

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
	 (head (make-cell! :name head-name :p 0 :q 0 :symb "0" :link "0"))
	 ;; The order is (n-1) first, (n-2) second, ... (0) last.
	 (symbols `(,@(reverse (loop for hn in (H0+) as m from 1 to (1- n) collect (cell-symb hn))) ,(cell-symb (h0))))
	 )
    (!! :jdeep "            .....J9n creating a list @~s from: ~s " head symbols)
    (loop for sym in symbols
	  with prev-cell = head
	  as next-cell-name = (newsym)
	  as next-cell = (make-cell! :name next-cell-name :p 0 :q 0 :symb sym :link "0")
	  do 
	  (setf (cell-link prev-cell) next-cell-name)
	  (setf prev-cell next-cell))
    (poph0 n)
    (ipush "H0" head-name)
    (!! :jdeep "            .....J9n created list: ")
    (!! :jdeep (pl head-name))))

(defun J11-helper-add-to-dlist (dlist-head att val &key (if-aleady-exists :replace)) ;; :error :allow-multiple
  (!! :jdeep "             .....ADD-TO-DLIST entry: dlisthead = ~s, att=~s, val=~s" dlist-head att val)
  (loop with next-att-cell = (cell-link dlist-head)
	with last-val-cell = dlist-head ;; In case we fall through immediately
	with next-val-cell = nil	;; gets set below
	until (zero? next-att-cell)
	do
	(setf next-att-cell (cell next-att-cell)) ;; Can't do this above bcs need zero? check
	(setf next-val-cell (cell (cell-link next-att-cell)))
	(!! :jdeep "             .....ADD-TO-DLIST is checking next-att-cell=~s, last-val-cell=~s" next-att-cell last-val-cell)
	(if (ipl-string-equal att (cell-symb next-att-cell))
	    (case if-aleady-exists
	      (:replace
	       (!! :jdeep "             .....In J11 (helper) replacing ~s symbol with ~s" next-val-cell val)
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
	  (!! :jdeep "             .....ADD-TO-DLIST taking the finally option: last-val-cell=~s, new-att-cell = ~s, new-val-cell=~s"
	      last-val-cell new-att-cell new-val-cell)
	  (setf (cell-link last-val-cell) (cell-name new-att-cell))
	  (H5+)
	  (return t))))

(defun j14-helper (att link)
  (if (zero? link) link ;; end of recursion
      (let* ((attcell (<== link))
	    (valcell (<== (cell-link attcell))))
	(if (string-equal att (cell-symb attcell))
	    ;; Skip the attribute and value cells, and return the link
	    ;; of the value.
	    (cell-link (<== (cell-link attcell)))
	    ;; If not, then skip to the valcell and recur, reinserting
	    ;; the result in the valcell's link, and then returning
	    ;; the attcell's link -- that is, the link we originally
	    ;; got, bcs that will be re-inserted above. Ugh.
	    (progn (setf (cell-link valcell)
			 (j14-helper att (cell-link valcell)))
		   link)))))

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

;;; WWW DESTRUCTIVE!!!!!!!!!!

(defun j181-helper-remove-non-numeric-except-first (s)
  (let* ((r (copy-seq " ")))
    (setf (aref r 0) (aref s 0)) ;; WWWWWWWWWWWWWWWWWWW
    (loop as p from 1 to (1- (length s))
	  as c = (aref s p)
	  do (if (numchar? c)
		 (setf r (format nil "~a~c" r c)))
	  finally (return r))))

(defun numchar? (c)
  (find c "0123456789"))

(defun w25-get () (numget (cell-symb (cell "W25"))))
(defun w25-set (n) (numset (cell-symb (cell "W25")) n))
(defun w25-init () (setf (cell-symb (cell "W25")) (cell-name (make-cell! :p 1 :q 2 :link 1))))

;;; These number things have to be given the name of what is supposed
;;; to be a numerical data cell, that is, one where the link is
;;; expected to be a number.

(defun numget (sym)
  (let* ((data-cell (cell sym))
	 (n (progn (!! :jdeep "Numget trying to  get the number from ~a" data-cell)
		   (cell-link data-cell))))
    (if (not (numberp n))
	(break "Numget was asked to get a non-number ~s from ~s (~s)." n data-cell sym)
	(if (>= n 0) n (break "Numget was asked to get a negative number ~a from  ~s (~s)." n data-cell sym)))))

(defun numset (sym n)
  (!! :jdeep "NUMSET asked to set ~s to ~s" sym n)
  (let* ((data-cell (cell sym)))
    (!! :jdeep "   ... NUMSET data cell is: ~s" data-cell)
    (unless (numberp (cell-link data-cell))
      (!! :jdeep "NUMSET asked to set ~s (via ~s) which doesn't already have a number in the link."
	  data-cell sym))
    (setf (cell-link data-cell) n (cell-p data-cell) 0) (cell-q data-cell) 1))

;;; !!! WWW OBIWAN UNIVERSE WITH LISP ZERO ORIGIN INDEXING WWW !!!
;;; (NNN H0p might be deprecated FFF Remove?)

(defun J183/4-Scanner ([0] mode)
  ;; NO POP H0! ("...leave (0)")
  (let* ((counter [0])
	 (w25p (W25-get)))
    (!! :jdeep "             .....Starting in J183/4-Scanner: counter = ~s, w25p = ~a" counter w25p)
    (if (not (numberp w25p)) (break "In J183/4 expected W25(p) (~a) to be a number.~%" (cell "W25")))
    (H5-)
    (incf w25p) ;; Start at W25+1 (per manual)
    (loop until (= w25p 80) 
	  ;; WWW OBIWON !!! The only place I should have to correct this is here (I hope!) 
	  as char = (aref *W24-Line-Buffer* (1- w25p))
	  do 
	  (!! :run-full "Deep in J183/4-Scanner: w25p = ~a, char = ~s" w25p char)
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
  (!! :jdeep "             .....Read into *W24-Line-Buffer*: ~s" *W24-Line-Buffer*))

(defun J2n=move-0-to-n-into-w0-wn (n)
  (loop for nn from 0 to n 
	as wcell-name in *w-cells*
	as HCell = (let ((top (H0))) (ipop "H0") top)
	;; FFF ??? Could use FORCE-REPLACE?
	do (ipop wcell-name) (ipush wcell-name (cell-symb HCell))))

(defun J3n=restore-wn (n)
  (loop for nn from 0 to n as wname in *w-cells* do (ipop wname)))

(defun J4n=preserve-wn (n)
  (loop for nn from 0 to n as wname in *w-cells* do (ipush wname)))

(defun J5n=preserve-wn-then-move-0-n-into-w0-wn (n)
  (J4n=preserve-wn n)
  (J2n=move-0-to-n-into-w0-wn n)
  )

(defun J73-shallow-copy-ipl-list (link)
  ;; This version doesn't honor Q=2
  (if (zero? link) link
      (let* ((old-cell (<== link))
	     (new-cell (make-cell!
			:p (cell-p old-cell)
			:q (cell-q old-cell)
			:symb (cell-symb old-cell)
			:link (J73-shallow-copy-ipl-list (cell-link old-cell))
			:id (cell-id old-cell))))
	(cell-name new-cell))))

;;; J74 copies the whole list structure, including honoring q=2
;;; symbols and making new locals for them when it comes across
;;; them. This is a bit conceptually pretzelly, so I replicate code
;;; more than I should to but will deal with that in a refactor.

(defun J74-deep-copy-ipl-list (link)
  ;; This always gets a symbol naming a cell that is a list head and
  ;; always returns the symbol to the new list head, which will be
  ;; connected into a new link (or symb for q=2) or, eventually,
  ;; returned as the top node of the whole copied list. Of course, in
  ;; the recursions, these list heads aren't the top of the graph.

  ;; Terminal case: Trying to copy things that can't ever be copied:
  ;; Functions, zeros (list ends), and regional symbols. (Regarding
  ;; regional symbols, you're thinking: "But if Q=2 then that needs to
  ;; be localized!". But that would have been done ABOVE here, so by
  ;; the time we get here, we would only be handed a regional symbol
  ;; if the above cell symb link was NOT q=2.

  (if (or (zero? link) ;; this first bcs "" screws regional-symbol?
	  (numberp link) ;; Actual numbers will only show up in data lists
	  (functionp (gethash link *symtab*))
	  (regional-symbol? link)) ;; This will have been replaced
				   ;; above if it was tagged q=2
      link

      ;; Okay, so we actually have a cell that needs to be
      ;; copied. Let's make a new one for it and then all we should
      ;; need to do is to fill it in, and do the correct recusions
      ;; through it's link, and, if q=2, it's symb. So far this is
      ;; just like J73 (although that only walks links, so we didn't
      ;; even need the special protections from regional symbols and
      ;; functions, as above.)

      (let* ((old-cell (<== link))
	     (old-name (cell-name old-cell))
	     (old-p (cell-p old-cell))
	     (old-q (cell-q old-cell))
	     (old-symb (cell-symb old-cell))
	     (old-link (cell-link old-cell))
	     (old-id (cell-id old-cell))
	     (new-cell-name (or (gethash old-name *j74tbl*) old-name))
	     (new-cell (make-cell!
			:name new-cell-name
			:p old-p
			:q old-q
			:symb :tbd
			:link (j74-deep-copy-ipl-list old-link)
			:id old-id)))

	;; Okay, now we have the new cell, and everything is correct
	;; EXCEPT the symb. The simple case is where q is NOT =2 nor
	;; is is local, in which case we just recurse on the symb and
	;; jam is in place. This is the part that may be able to be
	;; refactored.

	(if (or (not (= 2 old-q))
		(numberp old-symb)
		(local-symbol-by-name? old-symb))
	    (setf (cell-symb new-cell) (j74-deep-copy-ipl-list old-symb))
	    
	    ;; Okay, so now we have the difficult case where q=2 or
	    ;; (actually and/or) it's a local symbol. In thie case we
	    ;; need to create a new symbol and not only put it here,
	    ;; but also create a new subhead with that name, and copy
	    ;; in the info from the old sub-head, and then recurse
	    ;; down THIS cell. (??? WWW Possible screw case where it's
	    ;; q=2 but also a 0! I don't know why this would happen,
	    ;; but it's theoretically possible could.)

	    (let* ((old-sub-head (<== old-symb))
		   (new-subhead-name (setf (gethash old-symb *j74tbl*) (newsym))))
	      (make-cell!
	       :name new-subhead-name
	       :p (cell-p old-sub-head)
	       :q (cell-q old-sub-head)
	       :symb (cell-symb old-sub-head) ;; This will get checked
	       ;; on the recursion below.  This change here was a shot
	       ;; in the dark bcs *13 was being munged (B -> Q) and I
	       ;; thought maybe it was because of inappropriate
	       ;; sharing bcs a list wasn't being copied through it's
	       ;; links....or something, but it appears that this
	       ;; makes no difference.
	       :link (j74-deep-copy-ipl-list (cell-link old-sub-head)) 
	       :id (cell-id old-sub-head))
	      ;; Okay, so all we should have to do now is set this as
	      ;; the sym of the new-cell, and recursively copy from
	      ;; it.  ??? This is a little weird: It's gonna start
	      ;; from the new cell it just created. As a result, we're
	      ;; at least going to copy that cell TWICE...is this
	      ;; really necessary?! Could this recursion take place in
	      ;; the :symb set above??
	      (setf (cell-symb new-cell) (j74-deep-copy-ipl-list new-subhead-name))))
	;; And finally the result of the whole thing is just the new-cell-name.
	new-cell-name)))

(defun last-cell-of-linear-list (l)
  (cond ((zero? (cell-link l)) l)
	(t (last-cell-of-linear-list (cell (cell-link l))))))

;;; This only prints lists that are linked via their LINK symbols.

(defun pll (symb) (print-linear-list symb))
(defun print-linear-list (symb &optional (depth 0))
  (let ((cell (<== symb)))
    (if (numberp (cell-link cell))
	(format t "| ~s~70T|~%" cell)
	(progn 
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
	  ))))

(defun pl (symb &rest args)
    (format t "~%+------------------------- ~s ~s -------------------------+~%" symb (cell symb))
    (apply #'print-list symb args)
    (format t "+--------------------------End ~s -------------------------------------------+~%" symb)
    )
(defun print-list (symb &key (depth 0) (limit 3) (dls? t))
  (cond ((> depth limit) (format t "~a[@~a...]~%" (blanks (* (1- depth) 3)) depth))
	((or (not (atom symb))
	     (numberp symb)
	     (null symb)
	     (null (ignore-errors (cell symb)))
	     (zero? symb)))
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
		 (print-list (cell-link cell) :depth depth :limit limit) ;; Don't increment depth for the link
		 ;; (print-list (cell-link cell) :depth (1+ depth) :limit limit)
		 ))))))
	     
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
  (!! :run "********** Starting run at ~a with adv-limit = ~a **********" start-symb adv-limit)
  (setf *adv-limit* adv-limit)
  (setf *running?* t)
  (ipl-eval start-symb)
  (if (member :end-dump *!!*) (report-system-cells t))
  )

(defun initialize-machine ()
  (setf *running?* nil)
  (create-system-cells) ;; See above in storage section
  (H5+) ;; Init H5 +
  (setf (H3-cycles) 0 (cell-p (cell "H3")) 0 (cell-q (cell "H3")) 1) ;; Init H3 Cycle-Counter
  (setf *W24-Line-Buffer* (Blank80)) ;; Init Read Line buffer
  (w25-init) ;; I/O pointer
  (w26-init) ;; Trap action list (actually ignored, but needed for most complex code to work.)
  (setf *genstack* nil)
  (clrhash *jfn-calls*)
  )

;;; Trap action list (actually ignored, but needed for most complex code to work.)
(defun w26-init ()
  (make-cell! :name "W26" :symb (cell-name (make-cell! :name (newsym "W26") :symb "0" :link "0"))))

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
    ("60" "Copy of (0) replaces S; S lost; H0 n.c.")
    ("64" "Copy of (0) replaces S; S lost; H0 n.c. (==60)")
    ("70" "Goto by H5: -symb|+link itself")
    ))

(defun pq-explain (cell)
  (or (and (cell? cell)
	   (second (assoc (format nil "~a~a" (cell-p cell) (cell-q cell))
			  *pq-meanings* :test #'string-equal)))
      ""))

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
  (loop for arg in args
	if (or (numberp arg)
	       (string-equal "H0" arg)
	       (member arg *jfn-arg-traps* :test #'string-equal))
	do
	(???)
	(break "Arg ~s is either invalid or trapped! (WATCH OUT FOR H0 POP RACE!)~%" arg))
  args)

(defun ipl-eval (start-symb &aux s)
  (!! :run "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv Entering IPL-EVAL at ~s" start-symb)
  (prog (cell q p symb link)
     (ipush "H1" "exit")
     (ipush "H1" start-symb) ;; Where we're headed this time in.
     ;; Indicates (local) top of stack for hard exit (perhaps to recursive call)
   INTERPRET-Q 
     (!! :run-full "---> At INTERPRET-Q w/H1 = ~s! (*fname-hint* = ~s)" (H1) *fname-hint*)
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
			   (loop for arg in arglist
				 as val in (getstack "H0") ;; FFF %%% Walk this so we don't need the whole stack
				 collect (cell-symb val))))))
	   (when *fname-hint* 
	     (!! :jcalls (format t (if arglist "   .......... Calling ~a [~a]: ~s=~s~%"
				    "   .......... Calling ~a [~a] (No Args)~*~*~%")
			      *fname-hint* (getf (gethash *fname-hint* *jfn-plists*) 'explanation) arglist args))
	     (push args (gethash *fname-hint* *jfn-calls*)) ;; For (rj) summary reports
	     (maybe-break? *fname-hint*)
	     (setf *fname-hint* nil)
	     )
	   (apply fn args))
	 (push :ascend *card-cycles.ids-executed*)
	 (ipop "H1") ;; Remove the JFn call
	 (go ADVANCE)
	 ))
     (setq cell (cell (cell-symb (H1)))) ;; This shouldn't be needed since we're operating all in cell now.
     (!! :run "@~a~a >>>>> ~s (~a)~%" (H3-cycles) (H5) cell (pq-explain cell))
     (maybe-break? (cell-id cell))
     (setf *trace-instruction* cell) ;; For tracing and error reporting
     (setf p (cell-p cell)
	   q (cell-q cell)
	   symb (cell-symb cell)
	   link (cell-link cell)
	   )
     (!! :run-full "-----> At INTERPRET-Q: CELL =~s      Q = ~s, symb=~s~%" cell q symb)
     (case q
       ;; 0 take the symbol itself
       (0 (setf S symb) (go INTERPRET-P))
       ;; 1 Take the name the symbol is pointing to ???? THIS IS WRONG?
       (1 (setf S (cell-symb (cell symb))) (go INTERPRET-P))
       ;; 2 Take the symbol in the cell at the name that the symb is pointing to 
       (2 (setf S (cell-symb (cell (cell-symb (cell symb))))) (go INTERPRET-P))
       (3 (!! :run-full "(Unimplemented monitor action in ~s; Executing w/o monitor!)" cell) (setf S symb) (go INTERPRET-P))
       (4 (!! :run-full "(Unimplemented monitor action in ~s; Executing w/o monitor!)" cell) (setf S symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go ASCEND)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!" cell))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!" cell))
       )
   INTERPRET-P ;; p. 160
     (!! :run-full "     -----> At INTERPRET-P w/P = ~s, S=~s" p S)
     (!! :s "     -----> At INTERPRET-P w/P = ~s, S=~s" p S) ;; FFF Allow the keys to be a list
     (case p
       (0 (go TEST-FOR-PRIMITIVE))
       (1 (ipush "H0" S)) ;; Input S (after preserving HO) "A copy of

       (2 ;; Output to S (then restore HO)

	;; ********************************************************
	;; (0) is put in cell S; then H0 is restored." (Note: No S
	;; push!)  It's actually unclear what the right way to do this
	;; is. Here are two hypotheses; One works, the other doesn't,
	;; but I'm not sure I understand why. It actually seems to me
	;; that it should be the other way around!  There's something
	;; really wrong here since these ought to be identical, except
	;; that the force-replace creates a new cell. So someone
	;; someplace is holding a cell struct that shouldn't be, but
	;; apparently needs to be. UUU WWW !!! This bodes poorly for
	;; the overall correctness and stability of the interpreter!

	(setf (cell-symb (cell S)) (cell-symb (H0))) ;; THIS ONE WORKS!
	;; (force-replace S (cell-symb (H0)))        ;; THIS ONE DOES NOT WORK!

	(ipop "H0")
	)
	;; ******************************************************

       ;; "A copy of the symbol most recently stored in the push down
       ;; list of S is moved into S." (This is actually slightly
       ;; ambiguous -- if it's name wasn't "RESTORE" it could be
       ;; interpreted as COPYing the top of the S stack into S.)
       (3 (ipop S)) 
       (4 (ipush S))                         ;; Preserve (push down) S
       ;; REPLACE (0) BY S. A copy of S is put in HO; the current (0) is lost.
       (5 (setf (cell-symb (H0)) S))
       ;; "A copy of (0) is put in S; the current symbol in S is lost,
       ;; and (0) is unaffected." 
       (6 (setf (cell-symb (<== S)) (cell-symb (H0))))
       (7 (go BRANCH)) ;; Branch to S if H5-
       )
     (go ADVANCE)
   TEST-FOR-PRIMITIVE 
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (!! :run-full "-----> At TEST-FOR-PRIMITIVE w/S = ~s, Q = ~s, symb=~s" S q symb)
     (case q 
       (5 (setf link S) (go ADVANCE))
       (t (go DESCEND)))
   ADVANCE (!! :run-full "-----> At ADVANCE")
     (trace-cells)
     (if (and *adv-limit* (zerop (decf *adv-limit*)))
	 (break " !!!!!!!!!!!!!! IPL-EVAL hit *adv-limit* !!!!!!!!!!!!!!"))
     (incf (H3-cycles))
     (when (string-equal (cell-symb (h1)) "exit")
       (ipop "H1") ;; Remove the exit flag
       (!! :run "Exiting from IPL-EVAL ^^^^^^^^^^^^^^^^^^^^^^^^^^^")
       (return))
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (cell-link (cell (cell-symb (H1))))) ;; !!!!!!!! UGH !!!!!!!!
   ADVANCE-W/FORCED-LINK (!! :run-full "-----> At ADVANCE-W/FORCED-LINK (link=~s)" link)
     (setf *fname-hint* link)
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
     (!! :run-full "-----> At ASCEND w/H1 = ~s" (h1))
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (push :ascend *card-cycles.ids-executed*)
     (ipop "H1")
     (go ADVANCE)
   DESCEND 
     (push :descend *card-cycles.ids-executed*)
     (!! :run-full "-----> At DESCEND w/S = ~s" S)
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (setf *fname-hint* S)
     (ipush "H1" S) 
     (trace-cells)
     (go INTERPRET-Q)
   BRANCH
     (!! :run-full "-----> At BRANCH w/H5 = ~s, S= ~s" (H5) S)
     ;; Interpret Sign in H5: - H5-: Put S as LINK (control transfers to S); go
     ;; to ADVANCE. - H5+: Go to ADVANCE
     (when (string-equal (H5) "-") (setf link S) (go ADVANCE-W/FORCED-LINK))
     (go ADVANCE)
     ))

#|
;;; Note that this can't just replace the target, it has to make a
;;; copy and put that in place, because someone is likely to be
;;; holding the original.

(defun force-replace (tosymb fromsymb)
  (let* ((fromcell (<== fromsymb))
	 (new-cell (make-cell :symb fromsymb)))
    (!! :dr-memory "Force replacing ~s with ~s" tosymb new-cell)
    (setf (gethash tosymb *symtab*) new-cell)))
|#

(defun call-ipl-prim (symb)
  (break "!!!!!!!! UNIMPLEMENTED: (call-ipl-prim ~s)" symb))

;;; =========================================================================
;;; Utilities

(defun first-n (n l) (loop for i below n as e in l collect e))

(defun core-dump (table)
  (format t "~a contains ~a entries:~%" table (hash-table-count table))
  (loop for key being the hash-keys of table
	using (hash-value value)
	do (format t "~s => ~s~%" key value)))

(defun maybe-break? (s &aux (cycles (H3-cycles)))
  (push (cons cycles s) *card-cycles.ids-executed*)
  (when (or (equal t *breaks*)
	    (member t *breaks*)
	    (member cycles *breaks* :test #'equal)
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
  (declare (type integer scale))
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
                          (let ((line "")
				(*iscale (floor (* i scale))))
			    (declare (type fixnum *iscale))
                            ;; Scale horizontally
                            (loop for z across temp
                                  do (dotimes (s scale)
                                       (setf line (concatenate 'string line (string z)))))
                            ;; Add spacing
                            (setf line (concatenate 'string line 
                                                    (make-string (- (+ (* 3 scale) espace) (length line)) 
                                                                 :initial-element #\Space)))
                            ;; Append to output line
                            (setf (nth *iscale output)
				  (concatenate 'string (nth *iscale output) line))
                            
                            ;; Create bold effect for scaling
                            (loop for bold from 1 below scale
                                  do (setf (nth (+ *iscale bold) output)
                                           (nth *iscale output)))))))
      (format nil "~{~A~^~%~}" output))))

(defun announce (fmt &rest args)
  (format t "~%~A~%" (print-letters (apply #'format nil fmt args) 1 1)))


;;; =========================================================================
;;; Test calls

;;; Reminders: rsc rsc* (pll list-head-cell)

;;; Basic tracing setup for "light" tracing.

;;; t for all or :dr-memory :load :run :jdeep :run-full :io :end-dump :alerts :gentrace
(defparameter *default-!!list* '(:run :jcalls :alerts))

(defun set-trace-mode (&optional (mode :default))
  (untrace)
  (setf *trace-cell-names-or-exprs* nil)
  (setf *breaks* nil) ;; If this is set to t (or '(t)) it break on every call
  (setf *stack-depth-limit* 100) 
  (setf *stack-display-depth* 4)
  (setf *!!* *default-!!list*)
  (setf *report-all-system-cells?* nil)
  (setf *cell-tracing-on* nil)
  (setf *trace-exprs* nil)
  (case mode
    (:none (setf *!!* nil))))

;; Comment (or just ') progn blocks out as needed.

(progn ;; R3 from Newell et al. pp30-32
  (set-trace-mode :default)
  (setf *trace-cell-names-or-exprs* '("H0" "H1" "W0") *cell-tracing-on* t)
  (setf *!!* '(:run :jcalls)) ;; :dr-memory :s :run-deep :run-full :load :jdeep
  ;;(trace ipush ipop)
  (load-ipl "misccode/R3.liplv" :adv-limit 100)
  )

(progn ;; F1 test
  (set-trace-mode :none)
  ;(setf *!!* '() *cell-tracing-on* nil)
  ;(setf *!!* '(:run :run-full :dr-memory :jdeep :jcalls) *cell-tracing-on* t)
  ;(push :run-full *!!*)
  ;(trace ipush ipop force-replace)
  ;(setf *trace-cell-names-or-exprs* '("H0" "H1" "W0" "W1") *cell-tracing-on* t)
  (load-ipl "misccode/F1.liplv")
  )

(progn ;; Ackermann test
  (set-trace-mode :none)
  ;(set-trace-mode :default)
  ;(setf *trace-cell-names-or-exprs* '("H0" "A0" "K1" "M0" "N0") *cell-tracing-on* t)
  ;(setf *trace-exprs* '((9 (break))))
  ;(setf *!!* '(:run :jcalls)) ;; :dr-memory :s :run-deep :jdeep
  ;(trace numget numset ipush ipop poph0)
  (load-ipl "misccode/Ackermann.liplv" :adv-limit 25000)
  (print (cell "N0"))
  (if (= 61 (cell-link (cell "N0")))
      (format t "~%*********************************~%* Ackerman (3,3) = 61 -- Check! *~%*********************************~%")
      (error "Oops! Ackermann (3,3) should have been 61, but was ~s" (cell "N0")))
  )

'(progn ;; Test of call stack state machine. -- might be wrong!
  (set-trace-mode :default)
  (setf *trace-cell-names-or-exprs* '("H0" "H1") *cell-tracing-on* t)
  (trace ipush ipop)
  (load-ipl "misccode/T123.liplv" :adv-limit 100)
  )

'(progn ;; Test of EPAM
  (set-trace-mode :default)
  (setf *!!* '(:jdeep :run :jcalls) *cell-tracing-on* t)
  (load-ipl "EPAM/EPAMFixed.liplv" :adv-limit 10000)
  )

;;; WWW If this ends early with a BAD EXPRESSION (or other "normal
;;; error"), you're likely to get redisual errors from the loader
;;; trying to read more data after "normal" termination of the
;;; program.


#| Current issue (see notes.txt for the issue stack):


|#

;;; debugging tools: (pl cell) (pll cell) (rj) :c (ds) (trace!)
;;; list printing: (pl cell) (pll cell) [pll for linear lists only]
;;; (rx) analyzes routine call stats
;;; ?? tells you various values like H5 H3 H1 and H0 top and W1, W2, and W3
;;; *!!* <= :jdeep :run :jcalls :dr-memory :s :run-full :alerts :load :gentrace
;;; (fsym "symbol")

'(progn ;; LT 
  (set-trace-mode :default)
  ;;(setf *j15-mode* :clear-dl) ;; Documentation ambiguity, alt: :clear-dl :delete-dl
  ;; ************ NOTE P055R000 L11 HACK THAT MUST STAY IN PLACE! ************
  ;; (It's been over-riden by LTFixed code.)
  ;(setf *jfn-arg-traps* '("9-2941"))
  (setf *trace-exprs*
	'(
	  ;; ************ NOTE P055R000 L11 HACK THAT MUST STAY IN PLACE! ************
	  ;; See notes re special JFn:JP055R005JEFF (in LTFixed)
	  ;;("P055R000" (setf (cell-symb (car (H0+))) "L11")) ;; FFF should be patched in the original code!
  	  ;("P055R000" (???) (format t "~%~%") (backtrace! 25) (format t "~%~%") (pl (cell-symb (car (H0+)))))

	  ;; NOTE: The key can be partial, as "P052R"; uses
	  ;; (search...) for strings, or an expr, for example to trace
	  ;; when local is created: (= *gensym-counter* 3434)

	  ;; Here's a useful *trace-exprs*:
	  ;; ((= *gensym-counter* 3042) (???))

	  ;; Useful for localizing problems:
	  ;;((zerop (mod (h3-cycles) 100)) (print (h3-cycles)))

	  ;;("M088R020" (break))

	  ;; ((and (string-equal "0" (cell-symb (h0))) (string-equal "0" (cell-link (h0))))
	  ;;  (???))

	  ;; Basic tracer:

  	    ;; ("M001R000"
	    ;;  (setf *!!* '(:run :jcalls) *cell-tracing-on* t) ;; :run :jcalls :jdeep :alerts :s :gentrace
	    ;;  (setf *trace-cell-names-or-exprs* '("H0" "W0" "W1") *cell-tracing-on* t)  ;;    "W0" "W1" "W2" "W3"
	    ;;  )

	  ;;(2875 (break))

	  ;; Must call (trace-cell-safe-for-trace-expr) or (???) to
	  ;; trace cells otherwise messy recusion cycle ensues

	  ))
  (load-ipl "LT/LTFixed.liplv" :adv-limit 500000)
  )

;;; (load (compile-file "iplv.lisp"))

;;; Things not implemented: Aux storage, various J functions, 

;;; FFF Maybe use Lisp lists instead of the morass of symbol table pointers that
;;; require a mess of renaming.

;;; FFF Note that the dumper put multiple header lines in (:comments :type :name
;;; :sign :pq :symb :link :comments.1 :id). Prob. need code to ignore them
;;; rather than just skipping the first line.

(declaim (optimize (debug 3) (safety 3) (speed 0) (space 0) (compilation-speed 0)))

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

(defun new-symb-cell (symbol &optional (prefix "c"))
  (make-cell :name (symbol-name (gensym prefix)) :symb symbol))

(defparameter *symbol-col-accessors* `((cell-name . ,#'cell-name) (cell-symb . ,#'cell-symb) (cell-link . ,#'cell-link)))

(defun zero? (what)
  (member (if (stringp what) what
	      (cell-symb what))
	  '("" "0") :test #'string-equal))

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
	      (format nil " [~a/~a]" (cell-comments cell) (cell-comments cell)))))

;;; ===================================================================
;;; Symbol Table (and Stacks)
;;; ===================================================================

(defvar *symtab* (make-hash-table :test #'equal))

;;; *cell is symbol value for stacked symbols, like H0 and W0, used where there
;;; isn't a special macro for common ones.  WWW Note the convention of adding +
;;; when the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot try to
;;; push/pop things that aren't stacks!

(defmacro cell (symb) `(gethash ,symb *symtab*))
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

(defun ListX (l) ;; Get a list from it's name if necessary
  (if (listp l) l (stack l)))

;;; ===================================================================
;;; The Loader simply loads everything created by tsv2alist.py
;;; into *symtab*. Nb. You should end with a type 5 cell to execute!
;;; ===================================================================

(defvar *!!list* nil) ;; t for all, or: :load :run :run-full

(defun !! (key fmt &rest args)
  ;; WWW if the arg is actually nil, apply gets confused so we pre-fix this case.
  (unless args (setf args '(())))
  (when (or (equal *!!list* t)
	    (equal key t)
	    (member key *!!list*))
    (apply #'format t fmt args)
    (when (and (member key '(:run :run-full)) (member :run-full *!!list*))
      (report-system-cells))))

(defun report-system-cells ()
  (format t "~%  :: RUN REGISTERS ::")
  (loop for r in *system-cells*
	do (format t "  ~a+=~s ~a~%" r (cell r) (stack r)))
  (format t "  S=~s ~s~%" (s) (s+))
  )

(defvar *col->vals* (make-hash-table :test #'equal))
(defparameter *cols* '(:comments :type :name :sign :pq :symb :link :comments.1 :id))

(defvar *input-stream* nil) 

(defun load-ipl (file &key (reset? t) (load-mode :code))
  ;; Load-mode will be :code or :data as set by the latest type=5
  ;; cell's Q: Q=0=code, Q=1=data) And if the sym entry on a type 5
  ;; cell is filled, it's an execution start cell.
  (when reset? (reset!))
  (with-open-file
      (i file)
    (setf *input-stream* i) ;; For reads inside the program executor
    (!! :load "Loading IPL file: ~a~%" file)
    ;; First line is assumed to be the header which we just check
    (if (equal *cols* (read i))
	(!! :load "Header okay!~%")
	(error "No valid header on ~a" file)
	)
    (loop for read-row = (read i nil nil)
	  with cells = nil
	  until (null read-row)
	  do
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
		    (!! :load "Loading global name: ~a~%" name)
		    (save-cells (reverse cells) load-mode) (setf cells nil)
		    )
	      	  (push cell cells))
		(if (string-equal "5" (cell-type cell))
		    (if (global-symbol? (cell-symb cell))
			(progn
			  (format t "** Execution start at ~a **~%" (cell-symb cell))
			  (save-cells (reverse cells) load-mode)
			  (setf cells nil)
			  (run (cell-symb cell)))
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

(defun save-cells (cells load-mode)
  (setf load-mode :data) ;; ****************************************************************
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
      (setf (gethash top-name *symtab*) (car cells)) ;; ***********************************************
      (!! :load "Saved: ~a~%" (cell-name (car cells)))
      (when (eq :data load-mode)
	;; Loop through the whole list and create aa local symbol for
	;; every cell that doesn't already have one. This has to do a
	;; messy look ahead.
	(loop for (this-cell next-cell) on cells
	      as this-link = (cell-link this-cell)
	      as next-name = (when next-cell (cell-name next-cell))
	      when next-cell ;; This usually isn't needed anyway bcs there should be a 0
	      do (if (zero? this-link)
		     (if (zero? next-name)
			 (let ((new-symbol (new-list-symbol top-name)))
			   (setf (cell-name next-cell) new-symbol)
			   (setf (cell-link this-cell) new-symbol))
			 (setf (cell-link this-cell) next-name))))))
    (save-sublists cells)))

(defun new-list-symbol (&optional (prefix "")) (format nil "~a~a" prefix (gensym "+")))

(defun save-sublists (l)
    (loop for cells on l
	  as name = (cell-name (car cells))
	  unless (zero? name)
	  do (setf (gethash name *symtab*) (car cells)) ;; ***************************************************
	  (!! :load "Saved sublist: ~a~%" name)))

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
  (and (not (zerop (length name)))
       (char-equal #\9 (aref name 0))))

(defun uniquify-list (l)
  (loop for i on l
	unless (member (car i) (cdr i) :test #'equal)
	collect (car i)))

(defun reset! ()
  (clrhash *symtab*) 
  (setup-j-fns)
  (clrhash *col->vals*)
  )

;;; Note that (S) is not a system cell(stack) but just a
;;; symbol(stack).

(defparameter *system-cells* '("H0" "H1" "W0" "H5" "S"))

(defvar *systacks* (make-hash-table :test #'equal))

(defun create-system-cells ()
  (loop for name in *system-cells*
	do (setf (cell name) (make-cell :name name))
	(setf (gethash name *systacks*) (list (format nil "~a-empty" name)))
	(format t "Created system cell: ~s and its stack.~%" name)))

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
;;; ===================================================================

(eval-when (:execute :load-toplevel :compile-toplevel)
  (defmacro defj (name &rest forms)
    `(setf (gethash (string-upcase (format nil "~a" ',name)) *symtab*)
	   (lambda (arg0 arg1)
	     (!! :jfns ,(format nil "Calling ~a w/ARG0=~~s, ARG1=~~s~%" name) arg0 arg1)
	     ,@forms)))
  )

(defun setup-j-fns ()

  (defj J2 (!! :jfns "WWW J2 IS UNIMPLEMENTED !!!~%"))
  (defj J3 (!! :jfns "WWW J3 IS UNIMPLEMENTED !!!~%"))
  (defj J4 (!! :jfns "WWW J4 IS UNIMPLEMENTED !!!~%"))
  (defj J5 (!! :jfns "WWW J5 IS UNIMPLEMENTED !!!~%"))
  (defj J7 (!! :jfns "WWW J7 IS UNIMPLEMENTED !!!~%"))
  (defj J8 (!! :jfns "WWW J8 IS UNIMPLEMENTED !!!~%"))
  (defj J9 (!! :jfns "WWW J9 IS UNIMPLEMENTED !!!~%"))
  (defj J10 (!! :jfns "WWW J10 IS UNIMPLEMENTED !!!~%"))
  (defj J11 (!! :jfns "WWW J11 IS UNIMPLEMENTED !!!~%"))
  (defj J14 (!! :jfns "WWW J14 IS UNIMPLEMENTED !!!~%"))
  (defj J17 (!! :jfns "WWW J17 IS UNIMPLEMENTED !!!~%"))
  (defj J18 (!! :jfns "WWW J18 IS UNIMPLEMENTED !!!~%"))
  (defj J19 (!! :jfns "WWW J19 IS UNIMPLEMENTED !!!~%"))

  ;; Restore W0-Wn
  (defj J31 (!! :jfns "WWW J31 IS UNIMPLEMENTED !!!~%"))
  (defj J32 (!! :jfns "WWW J32 IS UNIMPLEMENTED !!!~%"))
  (defj J33 (!! :jfns "WWW J33 IS UNIMPLEMENTED !!!~%"))
  (defj J34 (!! :jfns "WWW J34 IS UNIMPLEMENTED !!!~%"))
  (defj J35 (!! :jfns "WWW J35 IS UNIMPLEMENTED !!!~%"))
  (defj J36 (!! :jfns "WWW J36 IS UNIMPLEMENTED !!!~%"))
  (defj J38 (!! :jfns "WWW J38 IS UNIMPLEMENTED !!!~%"))

  (defj J41 (!! :jfns "WWW J41 IS UNIMPLEMENTED !!!~%"))
  (defj J42 (!! :jfns "WWW J42 IS UNIMPLEMENTED !!!~%"))
  (defj J43 (!! :jfns "WWW J43 IS UNIMPLEMENTED !!!~%"))
  (defj J50 (!! :jfns "WWW J50 IS UNIMPLEMENTED !!!~%"))
  (defj J51 (!! :jfns "WWW J51 IS UNIMPLEMENTED !!!~%"))
  (defj J64 (!! :jfns "WWW J64 IS UNIMPLEMENTED !!!~%"))
  (defj J65 (!! :jfns "WWW J65 IS UNIMPLEMENTED !!!~%"))
  (defj J68 (!! :jfns "WWW J68 IS UNIMPLEMENTED !!!~%"))
  (defj J71 (!! :jfns "WWW J71 IS UNIMPLEMENTED !!!~%"))
  (defj J72 (!! :jfns "WWW J72 IS UNIMPLEMENTED !!!~%"))
  (defj J74 (!! :jfns "WWW J74 IS UNIMPLEMENTED !!!~%"))
  (defj J75 (!! :jfns "WWW J75 IS UNIMPLEMENTED !!!~%"))
  (defj J76 (!! :jfns "WWW J76 IS UNIMPLEMENTED !!!~%"))
  (defj J78 (!! :jfns "WWW J78 IS UNIMPLEMENTED !!!~%"))

  ;; Find the nth symbol on list (0)
  (defj J81 (!! :jfns "WWW J81 (Find Symbol in List) IS UNIMPLEMENTED !!!~%"))
  (defj J82 (!! :jfns "WWW J82 (Find Symbol in List) IS UNIMPLEMENTED !!!~%"))

  ;; Create a list of n symbols. (n-1) to (0) ???
  (defj J91 (!! :jfns "WWW J91 (Create list) IS UNIMPLEMENTED !!!~%"))

  (defj J111 (!! :jfns "WWW J111 IS UNIMPLEMENTED !!!~%"))
  (defj J115 (!! :jfns "WWW J115 IS UNIMPLEMENTED !!!~%"))
  (defj J116 (!! :jfns "WWW J116 IS UNIMPLEMENTED !!!~%"))
  (defj J124 (!! :jfns "WWW J124 IS UNIMPLEMENTED !!!~%"))
  (defj J125 (!! :jfns "WWW J125 IS UNIMPLEMENTED !!!~%"))
  (defj J130 (!! :jfns "WWW J130 IS UNIMPLEMENTED !!!~%"))
  (defj J133 (!! :jfns "WWW J133 IS UNIMPLEMENTED !!!~%"))
  (defj J136 (!! :jfns "WWW J136 IS UNIMPLEMENTED !!!~%"))
  (defj J137 (!! :jfns "WWW J137 IS UNIMPLEMENTED !!!~%"))
  (defj J138 (!! :jfns "WWW J138 IS UNIMPLEMENTED !!!~%"))

  ;; Tracing
  (defj J147 (!! :jfns "WWW J147 (Tracing) IS UNIMPLEMENTED !!!~%"))
  (defj J148 (!! :jfns "WWW J148 (Tracing) IS UNIMPLEMENTED !!!~%"))
  
  (defj J155 (!! :jfns "WWW J155 IS UNIMPLEMENTED !!!~%"))
  (defj J157 (!! :jfns "WWW J157 IS UNIMPLEMENTED !!!~%"))
  (defj J160 (!! :jfns "WWW J160 IS UNIMPLEMENTED !!!~%"))
  (defj J161 (!! :jfns "WWW J161 IS UNIMPLEMENTED !!!~%"))
  (defj J176 (!! :jfns "WWW J176 IS UNIMPLEMENTED !!!~%"))
  (defj J181 (!! :jfns "WWW J181 IS UNIMPLEMENTED !!!~%"))
  (defj J183 (!! :jfns "WWW J183 IS UNIMPLEMENTED !!!~%"))
  (defj J184 (!! :jfns "WWW J184 IS UNIMPLEMENTED !!!~%"))

  (defj J6 ;; REVERSE (0) and (1) WWW H1 is not (1)
      (let ((z (H0)))
	(setf (H0) (second (H0+)))
	(setf (second (H0+)) z)))

  (defj J66 
      ;; J66 INSERT (0) AT END OF LIST (1) IF NOT ALREADY ON IT. A
      ;; search of list (1) is made. against (0) (starting with the
      ;; cell after cell (1) . If (0) is found, J66 does nothing
      ;; further. If (0) is not found, it is inserted at the end of
      ;; the list, as in J65. (??? What happens if the list
      ;; branches??? At the moment this can't do anything sensible
      ;; with a branching list!)
      (!! :jfns "J66 trying to insert ~s in ~s~%" arg0 arg1)
      (let ((l (stack arg1)))
	(loop for cell in l
	      do (cond ((string-equal (cell-symb cell) arg0)
			(!! "J66 found ~s in the list already. No action!~%" arg0)
			(return nil))
		       ((zero? (cell-link cell))
			(!! "J66 hit end, adding ~s to the list!~%" arg0)
			(let* ((new-name (new-list-symbol arg1))
			       (new-cell (make-cell :name new-name :symb arg0 :link "0")))
			  (setf (cell-link cell) new-name)
			  (setf (stack new-name) new-cell)
			  (setf (stack arg1) `(,@l ,new-cell)))))))
      )

  (defj J73 ;; Copy list
      (setf (H0)
	    (copy-list
	     (if (stringp arg0) (stack arg0)
		 (if (listp arg0) arg0
		     (error "J73 got ARG0=~s" arg0))))))

  (defj J60
      ;; LOCATE NEXT SYMBOL AFTER CELL (0). (0) is the name of a
      ;; cell. If a next cell exists (LINK of (0) not a termination
      ;; symbol), then the output (0) is the name of the next cell,
      ;; and H5 is set +. If LINK is a termination symbol, then the
      ;; output (0) is the input (0), which is the name of the last
      ;; cell on the list, and H5 is set -. If the next cell is a
      ;; private termination cell, J60 will work as specified above,
      ;; but in addition, the private termination cell will be
      ;; returned to available space and the LINK of the input cell
      ;; (0) will be changed to hold 0. No test is made to see that
      ;; (0) is not a data term, and J60 will attempt to interpret a
      ;; data term as a standard IPL cell.
      (setf (h5) "+")
    (let* ((this-cell arg0)
	   (link (cell-link this-cell)))
	(!! :jfns "In J60, this-cell = ~s, link = ~s~%" this-cell link)
	(if (zero? link)
	    (setf (h5) "-")
	    (setf (H0) (cell link)) ;; (h5) is already + from above
	    )))

  (defj J74 ;; Copy List Structure
      ;; COPY LIST STRUCTURE (0). A new list structure is produced, the cells of
      ;; which are in one-to-one correspondence with the cells of list structure
      ;; (0). All the regional and internal symbols in the cells will be identical
      ;; to the symbols in the correspon- ding cells of (0), as will the contents of
      ;; data terms. There will be new local symbols, since these are the names of
      ;; the sublists of the new structure. Description lists will be copied, if
      ;; their names are local. If (0) is in auxiliary storage (Q of (0) = 6 or 7),
      ;; the copy will be produced in main storage. In all cases, list structure (0)
      ;; remains unaffected. The output (0) names the new list structure. It is
      ;; local if the input (0) is local; It is internal otherwise.
      (!! :jfns "J74 is copying list: ~s~%" (H0))
      (setf (H0) (copy-list-structure (H0)))
      )

  (defj J90
      ;; J90 creates an empty list (also used to create empty storage cells, and empty data terms).
      ;; The output (0) is the name a the new list.
      (let* ((name (new-list-symbol "L"))
	     (cell (make-cell :name name :symb "0" :link "0")))
	(!! :jfns "J90 creating blank list ~s~%" name)
	(setf (cell name) cell)
	(push cell (H0+))))

  (defj J100
      ;; J100 GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0). The subprocess
      ;; named (0) is performed successively with each of the symbols of list named
      ;; (1) as input. The order is the order on the list, starting with the first
      ;; list cell. H5 is always set + at the start of the subprocess. J100 will
      ;; move in list (1) if it is on auxiliary.
      (loop with subcall = (H0)
       	    for elt in (listX arg1)
       	    do
	    (push elt (H0+))
	    (ipl-eval arg0)
	    (pop (H0+))
	    ))

  (defj J120
      ;; COPY (0). The output (0) names a new cell containing the identical
      ;; contents to (0). The name is local if the input (0) is local; other-
      ;; wise, it is internal.
      (let ((new-cell (copy-cell (H0))))
	(setf (cell-name new-cell) (new-list-symbol))
	(setf (H0) new-cell)))

  (defj J151 ;; Print list (0)
      (mapcar #'print arg0))

  (defj J154
      ;; Clear Print Line CLEAR PRINT LINE. Print line 1W24 is cleared and the
      ;; current entry column, 1W2S, is set equal to the left margin, 1W21.
      (format t "WWW J154 (Clear Print Line) is UNIMPLEMENTED !!!~%"))

  (defj J180 ;; READ LINE J180 READLINE. The next record on unit 1W18 is read to
      ;; line 1W24. (The record is assumed to be BCD, 80 cols.) Column 1 of the
      ;; record is read into column 1 of the read line, and so forth. H5 is
      ;; set+. If no record can be read (end-of-file condition), the line is not
      ;; changed and HS is set - .
      (let ((line (read-line *input-stream* nil nil)))
	(!! :io "J180 Read:~%~s~%%" line)
	(cond (line
	       (push line (stack "W24"))
	       (setf (cell-symb (h5)) "+"))
	      (t (setf (cell-symb (h5)) "-")))))
  )

;;; Copying an IPL list is a tricky because they aren't represented like normal
;;; lisp lists (maybe they shold be?) but instead are a pile of cells where
;;; internal structure results from the symb and links pointing to other named
;;; cells all at the top level. In order to do this we need scan the whole list
;;; recursviely and create new symbols at each point. The only situation where
;;; we don't need to fill in an explicit pointer is when the list points to the
;;; NEXT element, but we do that anyway. All lists ground out on a 0 in the symb
;;; or link.

(defun copy-list-structure (l)
  (if (zero? l) l ;; End of sublist, just return the EOsL "0"
      (let ((new-name (new-list-symbol)))
	(setf (gethash new-name *symtab*) (mapcar #'copy-list-cell l))
	new-name)))

(defun copy-list-cell (cell)
  (if (zero? cell) cell ;; End of sublist, just return the EOsL "0"
      (let* ((new-cell (copy-cell cell)))
	(setf (cell-name new-cell) (new-list-symbol))
	;; WWW ??? This has the problem that it's going to copy whole functions
	;; into copied lists, which is probably not what is intended. Maybe
	;; things that are defined in the load process shouldn't be copied? 
	(setf (cell-symb new-cell) (copy-list-structure (cell-symb cell)))
	(setf (cell-link new-cell) (copy-list-structure (cell-link cell)))
	)))
	
;;; ===================================================================
;;; This is the core of the emulator. It directly implements "3.15 THE
;;; INTERPRETATION CYCLE", pg. 164 of the IPL-V manual. This is actually kinda
;;; ridiculous with the whole H1 descending and ascending mess. A "modern"
;;; evaluator would simply recurse. Maybe when I get sick enough of this mess,
;;; I'll recode it correctly. (IPL-EVAL can actually be called recursively...but
;;; the caller has to keep track of H1.
;;; ===================================================================

(defun run (start-symb)
  (initialize-machine)
  (ipl-eval (cell start-symb)))

(defun initialize-machine ()
  (create-system-cells)
  (setf (h5+) (list "+"))
  )

(defun ^^ (ssname)
  (setf (cell ssname) (pop (stack ssname))))
(defun vv (ssname &optional new-value)
  (push (cell ssname) (stack ssname))
  (when new-value (setf (cell ssname) new-value)))

(defun ipl-eval (start-cell)
  (!! :run "Entering IPL-EVAL at ~a vvvvvvvvvvvvvvv" start-cell)
  (prog (cell pq q p symb link)
     (push (new-symb-cell "exit") (h1+)) ;; Top of stack -- force exit (may be recursive)
     (vv "H1" start-cell) ;; Where we're headed this time in.
     ;; Indicates (local) top of stack for hard exit (perhaps to recursive call)
   INTERPRET-Q 
     (!! :run-full "---> At INTERPRET-Q w/H1 = ~s!~%" (h1))
     ;; H1 contains the name of the cell holding the instruction to be
     ;; interpreted. At this point it could be a symbol or a list. If it's a
     ;; symbol, we need to de-reference it to the list. In the case of an
     ;; internal (J) funtion this will be a lambda, in which case we just call
     ;; it and then advance
     (when (null (H1)) (break "!!! PROBABLY MISSING A JFN DEFINITION !!!"))
     (when (functionp (h1))
       (funcall (H1) (H0) (first (H0+))) ;; Call the fn passing the top and second cells in H0 as Arg0 and Arg1
       (^^ "H1") ;; Remove the JFn call
       (go ADVANCE)
       )
     (setq cell (H1)) ;; This shouldn't be needed since we're operating all in cell now.
     (when (member :pre-exec-dump *!!list*)
       (format t "~%============== STATE BEFORE NEXT EXEC ==============~%")
       (report-system-cells))
     (!! :run "~%~%>>>>>>>>>>~%      Executing cell: ~s~%~%" cell)
     (setf pq (cell-pq cell)
	   q (getpq :q pq)
	   p (getpq :p pq)
	   symb (cell-symb cell)
	   link (cell-link cell)
	   )
     (!! :run-full "~%-----> At INTERPRET-Q: CELL =~s;" cell)
     ;; NNN Note that all the following are separate code segments -- we jump
     ;; around, never passing through to the next section.
     ;; INTERPRET-Q: - Q = 0, 1, 2: Apply Q to SYMBto yield S; go to
     ;; INTERPRET-P.  - Q = 3, 4: Execute monitor action (see ~ 15.0,
     ;; MONITORSYSTEM) ; take S = SYMB; go to INTERPRET-P.  - Q = 5:
     ;; Transfer machine control to SYMB (executing primitive); go to
     ;; ASCEND.  - Q = 6, 7: Bring blocks of routines in from auxiliary
     ;; storage; put location of routine in block into Hl; go to
     ;; INTERPRET-Q.
     (!! :run-full "   w/Q = ~s, symb=~s~%" q symb)
     (case q
       ;; 0 take the symbol itself
       (0 (setf (s) symb) (go INTERPRET-P))
       ;; 1 Take the name the symbol is pointing to
       (1 (setf (s) (cell-name (cell symb))) (go INTERPRET-P))
       ;; 2 Take the symbol in the cell at the name that the symb is pointing to
       (2 (print (list "----------------------" symb (cell symb) (cell-name (cell symb)) (cell (cell-name (cell symb)))))
	  (setf (s) (cell-symb (cell (cell-name (cell symb))))) (go INTERPRET-P))
       (3 (format t "Unimplemented monitor action in ~s; Executing w/o monitor!~%" cell) (setf (s) symb) (go INTERPRET-P))
       (4 (format t "Unimplemented monitor action in ~s; Executing w/o monitor!~%" cell) (setf (s) symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go ASCEND)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!" cell))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!" cell))
       )
   INTERPRET-P 
     (!! :run-full "-----> At INTERPRET-P w/P = ~s, (s)=~s~%" p (s))
     ;; - P = 0: Go to TEST FOR PRIMITIVE. - P=1, 2, 3, 4, 5, 6: Perform the
     ;; - operation; go to  ADVANCE. - P = 7: Go to BRANCH.
     (case p
       (0 (go TEST-FOR-PRIMITIVE))
       (1 ;; Input S (after preserving HO) ;; ??? Hopefully "input" means to push it on the stack ???
	(vv "H0" (s)))
       (2 ;; Output to S (then restore HO)
	(setf (s) (h0)) (^^ "H0"))
       (3 ;; Restore (pop up) S 
	(^^ "S"))
       (4 ;; Preserve (push down) S
	(vv "S"))
       (5 ;; Replace (0) by S -- Here we need to make a cell to hold S
	  ;; because it's just a list symbol (string, actually)
	(setf (H0) (new-symb-cell (s))))
       (6 ;; Copy (0) in S -- This is the opposite of 5, and we need
	  ;; to unpack the cell into the symbol.
	(setf (s) (cell-symb (H0))))
       (7 ;; Branch to S if H5-
	(go BRANCH)) ;;; ??? WWW The 3.15 and cheat sheet slightly disagree on this ??? WWW
       )
     (go ADVANCE)
   TEST-FOR-PRIMITIVE 
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (!! :run-full "-----> At TEST-FOR-PRIMITIVE w/S = ~s, Q = ~a, symb=~s~%" (s) q symb)
     (case q 
       (5 (setf link (s)) (go ADVANCE))
       (t (go DESCEND)))
   ADVANCE (!! :run-full "-----> AtADVANCE")
     (when (string-equal (cell-symb (h1)) "exit")
       (!! :run-full "Exiting from IPL-EVAL ^^^^^^^^^^^^^^^")
       (^^ "H1") (return))
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (cell-link cell))
     (!! :run-full "In ADVANCE: LINK = ~a~%" link)
     ;; If link is nil ("") in the middle of a function, go next cell, else ascend.
     (if (zero? link)
	 (if (break "(null (h1))") ;; WWW THIS CAN'T BE RIGHT !!!
	     (go ASCEND)
	     (^^ "H1"))
	 ;; Note that if there is a link to a different function
	 ;; (commonly J31, which resets W0 and W1), then when THAT
	 ;; function terminates the whole prog sequence
	 ;; ascends. This is a somewhat confusing yet common way to
	 ;; end a function, that is, by branching off to a J
	 ;; function which, when it completes, pops to whereever its
	 ;; caller came from.
	 (setf (h1) (cell link))
	 )
     (go INTERPRET-Q)
     ;; FFF ASCEND and DESCEND could probably be handled more cleanly and
     ;; correctly by recursing on IPL-EVAL !!!
   ASCEND 
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (^^ "H1")
     (!! :run-full "-----> AtASCEND w/H1 = ~a~%" (h1))
     (go ADVANCE)
   DESCEND 
     (!! :run-full "-----> AtDESCEND w/S = ~a~%" (s))
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (vv "H1" (cell (s)))
     (go INTERPRET-Q)
   BRANCH 
     (!! :run-full "-----> AtBRANCH w/H5 = ~a, S= ~a~%" (h5) (s))
     ;; Interpret Sign in H5: - H5-: Put S as LINK (control transfers to S); go
     ;; to ADVANCE. - H5+: Go to ADVANCE
     (when (string-equal (h5) "-") (setf link (s)))
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

(untrace)
(trace ipl-eval run)
(setf *!!list* '(:pre-exec-dump :load :run :jfns :run-full :io)) ;; :pre-exec-dump :load :run :jfns :run-full :io
;(load-ipl "LTFixed.lisp")
(load-ipl "F1.lisp")

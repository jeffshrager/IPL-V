;;; (load (compile-file "iplv.lisp"))

;;; Things not implemented: Aux storage, various J functions, 

;;; FFF Maybe use Lisp lists instead of the morass of symbol table pointers that
;;; require a mess of renaming.

(declaim (optimize (debug 3) (safety 3) (speed 0) (space 0) (compilation-speed 0)))

(defstruct (card (:print-function print-card)) comments type name sign pq symb link comments.1 id)
(defparameter *symbol-col-accessors* `((card-name . ,#'card-name) (card-symb . ,#'card-symb) (card-link . ,#'card-link)))

(defun print-card (card s d)
  (declare (ignore d))
  (format s "{~a::~a/~a/~a/~a [~a/~a]}"
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

(defvar *symtab* (make-hash-table :test #'equal))

;;; Symbol is a short hand for getting symbol values from the *symtab* (FFF
;;; Think about using the lisp symbol table instead of *symtab*. Collisions are
;;; extremely unlikely with everything called W0, M13, and J123! :-)

(defmacro symval (symb) `(gethash ,symb *symtab*))

;;; *val is symbol value for stacked symbols, like H0 and W0, used where there
;;; isn't a special macro for common ones.  WWW Note the convention of adding +
;;; when the var has the whole stack. System symbols (machine stacks) are
;;; strings just like user-defined symbols. It's up to the user to ot try to
;;; push/pop things that aren't stacks!

(defmacro *val+ (symb) `(gethash ,symb *symtab*)) ;; + Version gets the whole stack
(defmacro *val (symb) `(car (*val+ ,symb)))

;;; Important values it have special macros (these are like (h0) = (0) in the
;;; IPL-V manual). The ...+ fns return the whole stack. (Note that you'll have
;;; to get (1), that is, the second stack entry in H0 manually!)

(defmacro h0+ () `(*val+ "h0"))
(defmacro h0 () `(*val "h0"))
(defmacro h1+ () `(*val+ "h1"))
(defmacro h1 () `(*val "h1"))
(defmacro h5+ () `(*val+ "h5"))
(defmacro h5 () `(*val "h5"))
(defmacro s+ () `(*val+ "s"))
(defmacro s () `(*val "s"))

(defun ListX (l) ;; Get a list from it's name if necessary
  (if (listp l) l (*val+ l)))

;;; ===================================================================
;;; The Loader simply loads everything created by tsv2alist.py
;;; into *symtab*. Nb. You should end with a type 5 card to execute!
;;; ===================================================================

(defvar *ipl-trace-list* nil) ;; t for all, or: :load :run :run-full

(defun ipl-trace (key fmt &rest args)
  ;; WWW if the arg is actually nil, apply gets confused so we pre-fix this case.
  (unless args (setf args '(())))
  (when (or (equal *ipl-trace-list* t)
	    (equal key t)
	    (member key *ipl-trace-list*))
    (apply #'format t fmt args)
    (when (and (member key '(:run :run-full))
	       (member :run-full *ipl-trace-list*))
      (report-important-registers))))

(defparameter *important-run-registers* '("h1" "h0" "h5" "s"))
(defun report-important-registers ()
  (format t "~%vvvvv RUN REGISTERS vvvvv~%")
  (loop for r in *important-run-registers*
	do (format t "  ~a* = ~s~%" r (*val+ r)))
  (format t "~%^^^^^^^^^^^^^^^^^^^^^^^^^~%")
  )

(defvar *col->vals* (make-hash-table :test #'equal))
(defparameter *cols* '(:comments :type :name :sign :pq :symb :link :comments.1 :id))

(defvar *input-stream* nil) 

(defun load-ipl (file &key (reset? t))
  (when reset? (reset!))
  (with-open-file
      (i file)
    (setf *input-stream* i) ;; For reads inside the program executor
    (ipl-trace :load "Loading IPL file: ~a~%" file)
    ;; First line is assumed to be the header which we just check
    (if (equal *cols* (read i))
	(ipl-trace :load "Header okay!~%")
	(error "No valid header on ~a" file)
	)
    (loop for read-row = (read i nil nil)
	  with cards = nil
	  until (null read-row)
	  do
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
	    ;; Collect frequency of symbol use data.
	    (loop for col in *cols* as val in read-row
		  unless (string-equal "" val)
		  do (push val (gethash col *col->vals*)))
	    (cond ((string-equal "" (card-type card))
		   (when (global-symbol? name)
		     (ipl-trace :load "Loading global name: ~a~%" name)
		     (save-cards (reverse cards))
		     (setf cards nil))
	      	   (push card cards))
		  ((and (string-equal "5" (card-type card))
			(global-symbol? (card-symb card)))
		   (format t "*** Execution start at ~a ***~%" (card-symb card))
		   (save-cards (reverse cards))
		   (run (card-symb card)))
		  (t (ipl-trace :load "Ignoring: ~s~%" read-row))))
	  finally (save-cards (reverse cards))
	  )))

(defun save-cards (cards)
  ;; This does a really ugly hack (or, one might consider it a
  ;; clever hack?) Once we have the thing completely in hand, we
  ;; change the local symbols to FN_9-... and save those as separate
  ;; symtab entries. This allows the code to branch, and also run
  ;; through, and also use sub sections of code in J100 meta-calls
  ;; (ugh!)
  (when cards
    (let* ((top-name (card-name (car cards)))
	   (local-symbols.new-names
	    (uniquify-list
	     (loop for card in cards
		   append (loop for (nil . getter) in *symbol-col-accessors*
				as symbol = (funcall getter card)
				if (local-symbol? symbol)
				collect (cons symbol (format nil "~a-~a" top-name symbol)))))))
      (convert-local-symbols cards local-symbols.new-names)
      (setf (gethash top-name *symtab*) cards)
      (ipl-trace :load "Saved: ~a~%" (card-name (car cards)))
      (save-subcodes cards))))

;;; WWW %%% This is duplicative! Each sublist contains all the sublists after it.
;;; it!

(defun save-subcodes (l)
    (loop for cards on l
	  as name = (card-name (car cards))
	  unless (string-equal "" name)
	  do (setf (gethash name *symtab*) cards)
	  (ipl-trace :load "Saved subcode: ~a~%" name)))

;;; WWW This is used both on loading, and in list copying.

(defun convert-local-symbols (cards local-symbols.new-names)
  (labels ((replace-symbols (card accname.accessor)
	     (let ((new-name (cdr (assoc (funcall (cdr accname.accessor) card) local-symbols.new-names :test #'string-equal))))
	       (when new-name (setf* (car accname.accessor) card new-name)))))
    (loop for card in cards
	  do (loop for accname.accessor in *symbol-col-accessors*
		   do (replace-symbols card accname.accessor)))))
			    
;;; This stupidity is needed because setf doesn't know how to set a value based
;;; on an arbitrary accessor.

(defun setf* (accname card new-name)
  (case accname
    (card-name (setf (card-name card) new-name))
    (card-symb (setf (card-symb card) new-name))
    (card-link (setf (card-link card) new-name))))

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

;;; Loaded code analysis:

(defun report-col-vals ()
  (loop for col being the hash-keys of *col->vals*
	using (hash-value vals)
	collect (list col (sort (count-vals vals) #'> :key #'cdr))))

#| List of JFns by frequency:

> (mapcar #'(lambda (i) (when (char-equal #\J (aref (car i) 0)) (print i))) 
      (second (assoc :symb (report-col-vals))))

("J6" . 40) 
("J4" . 37) 
("J81" . 36) 
("J60" . 35) 
("J100" . 26) 
("J71" . 22) 
("J10" . 18) 
("J136" . 17) 
("J155" . 17) 
("J72" . 16) 
("J154" . 16) 
("J5" . 15) 
("J2" . 15) 
("J11" . 15) 
("J31" . 14) 
("J38" . 12) 
("J161" . 12) 
("J50" . 12) 
("J90" . 12) 
("J33" . 11) 
("J160" . 11) 
("J9" . 11) 
("J82" . 10) 
("J157" . 10) 
("J64" . 9) 
("J34" . 7) 
("J74" . 6) 
("J8" . 6) 
("J116" . 6) 
("J7" . 6) 
("J14" . 5) 
("J133" . 5) 
("J18" . 5) 
("J68" . 5) 
("J41" . 5) 
("J125" . 5) 
("J124" . 5) 
("J3" . 5) 
("J51" . 4) 
("J91" . 4) 
("J43" . 4) 
("J17" . 4) 
("J19" . 4) 
("J42" . 4) 
("J32" . 4) 
("J73" . 4) 
("J65" . 4) 
("J75" . 4) 
("J78" . 4) 
("J35" . 3) 
("J36" . 3) 
("J184" . 3) 
("J111" . 3) 
("J138" . 3) 
("J137" . 3) 
("J66" . 3) 
("J115" . 3) 
("J76" . 3) 

|#

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
  (defmacro defj (name &rest forms)
    `(setf (gethash (string-upcase (format nil "~a" ',name)) *symtab*)
	   (lambda (arg0 arg1)
	     (ipl-trace :jfns ,(format nil "Calling ~a w/ARG0=~~s, ARG1=~~s~%" name) arg0 arg1)
	     ,@forms)))
  )

(defun setup-j-fns ()

  (defj J2 (ipl-trace :jfns "WWW J2 IS UNIMPLEMENTED !!!~%"))
  (defj J3 (ipl-trace :jfns "WWW J3 IS UNIMPLEMENTED !!!~%"))
  (defj J4 (ipl-trace :jfns "WWW J4 IS UNIMPLEMENTED !!!~%"))
  (defj J5 (ipl-trace :jfns "WWW J5 IS UNIMPLEMENTED !!!~%"))
  (defj J6 (ipl-trace :jfns "WWW J6 IS UNIMPLEMENTED !!!~%"))
  (defj J7 (ipl-trace :jfns "WWW J7 IS UNIMPLEMENTED !!!~%"))
  (defj J8 (ipl-trace :jfns "WWW J8 IS UNIMPLEMENTED !!!~%"))
  (defj J9 (ipl-trace :jfns "WWW J9 IS UNIMPLEMENTED !!!~%"))
  (defj J10 (ipl-trace :jfns "WWW J10 IS UNIMPLEMENTED !!!~%"))
  (defj J11 (ipl-trace :jfns "WWW J11 IS UNIMPLEMENTED !!!~%"))
  (defj J14 (ipl-trace :jfns "WWW J14 IS UNIMPLEMENTED !!!~%"))
  (defj J17 (ipl-trace :jfns "WWW J17 IS UNIMPLEMENTED !!!~%"))
  (defj J18 (ipl-trace :jfns "WWW J18 IS UNIMPLEMENTED !!!~%"))
  (defj J19 (ipl-trace :jfns "WWW J19 IS UNIMPLEMENTED !!!~%"))
  (defj J31 (ipl-trace :jfns "WWW J31 IS UNIMPLEMENTED !!!~%"))
  (defj J32 (ipl-trace :jfns "WWW J32 IS UNIMPLEMENTED !!!~%"))
  (defj J33 (ipl-trace :jfns "WWW J33 IS UNIMPLEMENTED !!!~%"))
  (defj J34 (ipl-trace :jfns "WWW J34 IS UNIMPLEMENTED !!!~%"))
  (defj J35 (ipl-trace :jfns "WWW J35 IS UNIMPLEMENTED !!!~%"))
  (defj J36 (ipl-trace :jfns "WWW J36 IS UNIMPLEMENTED !!!~%"))
  (defj J38 (ipl-trace :jfns "WWW J38 IS UNIMPLEMENTED !!!~%"))
  (defj J41 (ipl-trace :jfns "WWW J41 IS UNIMPLEMENTED !!!~%"))
  (defj J42 (ipl-trace :jfns "WWW J42 IS UNIMPLEMENTED !!!~%"))
  (defj J43 (ipl-trace :jfns "WWW J43 IS UNIMPLEMENTED !!!~%"))
  (defj J50 (ipl-trace :jfns "WWW J50 IS UNIMPLEMENTED !!!~%"))
  (defj J51 (ipl-trace :jfns "WWW J51 IS UNIMPLEMENTED !!!~%"))
  (defj J60 (ipl-trace :jfns "WWW J60 IS UNIMPLEMENTED !!!~%"))
  (defj J64 (ipl-trace :jfns "WWW J64 IS UNIMPLEMENTED !!!~%"))
  (defj J65 (ipl-trace :jfns "WWW J65 IS UNIMPLEMENTED !!!~%"))
  (defj J66 (ipl-trace :jfns "WWW J66 IS UNIMPLEMENTED !!!~%"))
  (defj J68 (ipl-trace :jfns "WWW J68 IS UNIMPLEMENTED !!!~%"))
  (defj J71 (ipl-trace :jfns "WWW J71 IS UNIMPLEMENTED !!!~%"))
  (defj J72 (ipl-trace :jfns "WWW J72 IS UNIMPLEMENTED !!!~%"))
  (defj J74 (ipl-trace :jfns "WWW J74 IS UNIMPLEMENTED !!!~%"))
  (defj J75 (ipl-trace :jfns "WWW J75 IS UNIMPLEMENTED !!!~%"))
  (defj J76 (ipl-trace :jfns "WWW J76 IS UNIMPLEMENTED !!!~%"))
  (defj J78 (ipl-trace :jfns "WWW J78 IS UNIMPLEMENTED !!!~%"))
  (defj J81 (ipl-trace :jfns "WWW J81 IS UNIMPLEMENTED !!!~%"))
  (defj J82 (ipl-trace :jfns "WWW J82 IS UNIMPLEMENTED !!!~%"))
  (defj J90 (ipl-trace :jfns "WWW J90 IS UNIMPLEMENTED !!!~%"))
  (defj J91 (ipl-trace :jfns "WWW J91 IS UNIMPLEMENTED !!!~%"))
  (defj J111 (ipl-trace :jfns "WWW J111 IS UNIMPLEMENTED !!!~%"))
  (defj J115 (ipl-trace :jfns "WWW J115 IS UNIMPLEMENTED !!!~%"))
  (defj J116 (ipl-trace :jfns "WWW J116 IS UNIMPLEMENTED !!!~%"))
  (defj J124 (ipl-trace :jfns "WWW J124 IS UNIMPLEMENTED !!!~%"))
  (defj J125 (ipl-trace :jfns "WWW J125 IS UNIMPLEMENTED !!!~%"))
  (defj J130 (ipl-trace :jfns "WWW J130 IS UNIMPLEMENTED !!!~%"))
  (defj J133 (ipl-trace :jfns "WWW J133 IS UNIMPLEMENTED !!!~%"))
  (defj J136 (ipl-trace :jfns "WWW J136 IS UNIMPLEMENTED !!!~%"))
  (defj J137 (ipl-trace :jfns "WWW J137 IS UNIMPLEMENTED !!!~%"))
  (defj J138 (ipl-trace :jfns "WWW J138 IS UNIMPLEMENTED !!!~%"))
  (defj J155 (ipl-trace :jfns "WWW J155 IS UNIMPLEMENTED !!!~%"))
  (defj J157 (ipl-trace :jfns "WWW J157 IS UNIMPLEMENTED !!!~%"))
  (defj J160 (ipl-trace :jfns "WWW J160 IS UNIMPLEMENTED !!!~%"))
  (defj J161 (ipl-trace :jfns "WWW J161 IS UNIMPLEMENTED !!!~%"))
  (defj J176 (ipl-trace :jfns "WWW J176 IS UNIMPLEMENTED !!!~%"))
  (defj J181 (ipl-trace :jfns "WWW J181 IS UNIMPLEMENTED !!!~%"))
  (defj J183 (ipl-trace :jfns "WWW J183 IS UNIMPLEMENTED !!!~%"))
  (defj J184 (ipl-trace :jfns "WWW J184 IS UNIMPLEMENTED !!!~%"))

  (defj J73 ;; Copy list
      (setf (h0)
	    (copy-list
	     (if (stringp arg0) (*val+ arg0)
		 (if (listp arg0) arg0
		     (error "J73 got ARG0=~s" arg0))))))

  (defj J100
      ;; J100 GENERATE SYMBOLS FROM LIST (1) FOR SUBPROCESS (0). The subprocess
      ;; named (0) is performed successively with each of the symbols of list named
      ;; (1) as input. The order is the order on the list, starting with the first
      ;; list cell. H5 is always set + at the start of the subprocess. J100 will
      ;; move in list (1) if it is on auxiliary.
      (loop with subcall = (h0)
       	    for elt in (listX arg1)
       	    do
	    (push elt (h0+))
	    (ipl-eval arg0)
	    (pop (h0+))
	    ))

  (defj J120
      ;; COPY (0). The output (0) names a new cell containing the identical
      ;; contents to (0). The name is local if the input (0) is local; other-
      ;; wise, it is internal.
      (let ((l (if (stringp (h0)) (*val+ (h0)) (h0)))
	    (new-name (format nil "~a" (gensym "+"))))
	(ipl-trace :jfns "J120 created new list pointer ~s from ~s~%" new-name l)
	(setf (*val+ new-name) l)
	(setf (h0) new-name)))

  (defj J147 ;; Mark routine to trace
      (format t "WWW J147 (Mark routine to trace) is UNIMPLEMENTED !!!~%"))
  (defj J148 ;; Mark routine to propogate trace
      (format t "WWW J147 (Mark routine to propogate trace) is UNIMPLEMENTED !!!~%"))
  
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
	(ipl-trace :io "J180 Read:~%~s~%%" line)
	(cond (line
	       (push line (*val+ "W24"))
	       (setf (h5) "+"))
	      (t (setf (h5) "-")))))
  )

;;; Copying an IPL list is a tricky because they aren't represented like normal
;;; lisp lists (maybe they shold be?) but instead are a pile of cards where
;;; internal structure results from the symb and links pointing to other named
;;; cards all at the top level. In order to do this we need to go through and
;;; make a local symbol table, and then change all the symbols as we go. (If we
;;; knew that the list was guaranteed to be forward-pointing only, we could do
;;; this in one pass.) Importantly, not all symbols in a list point to the list
;;; itself, so we don't want to be changing those that don't! WWW We also have
;;; to chase every list pointed to by this one! Ugh!

(defun J74-copy-ipl-list**WRONG! (l &aux local-symbols.new-names)
  ;; *** THIS IS BROKEN -- IT NEEDS TO COPY THE ENTIRE LIST STRUCTURE ***
  ;; First pass make the symbol table of the names of symbols in the list
  ;; itself, and give them new names. These are the only ones we want to
  ;; change.
  (ipl-trace :run-full "Copying list: ~s~%" l)
  (loop for card in l
	as name = (card-name card)
	when (not (string-equal "" name))
	do (push (cons name (format nil "~a" (gensym "+")))
		 local-symbols.new-names))
  ;; Okay, so now all we need to do is copy the list an replace the names in
  ;; the cards with those in the symtab
  (let ((new-list
	 (loop for card in l
	       collect (convert-local-symbols cards local-symbols.new-names))))
    ;; Finally, register all the new partial lists in the symbtab
    (save-list-and-sublists l)
    ;; And return the new-list in (0)
    (ipl-trace :run-full "   ... New list: ~s~%" new-list)
    (setf (h0) new-list)
    ))
	
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
  (ipl-eval start-symb))

(defun initialize-machine ()
  (setf (h5+) (list "+"))
  )

(defun ipl-eval (start-symb)
  (ipl-trace :run "Entering IPL-EVAL at ~a vvvvvvvvvvvvvvv" start-symb)
  (prog (card pq q p symb link trace-name-temp)
     (push :exit (h1+)) ;; Top of stack -- force exit (may be recursive)
     (push start-symb (h1+)) ;; Where we're headed this time in..
     ;; Indicates (local) top of stack for hard exit (perhaps to recursive call)
     (push :s-top (s+))
   INTERPRET-Q (ipl-trace :run-full "*** INTERPRET-Q")
     (ipl-trace :run "INTERPRET-Q w/H1 = ~s!~%" (h1))
     ;; H1 contains the name of the cell holding the instruction to be
     ;; interpreted. At this point it could be a symbol or a list. If it's a
     ;; symbol, we need to de-reference it to the list. In the case of an
     ;; internal (J) funtion this will be a lambda, in which case we just call
     ;; it and then advance
     (setf trace-name-temp (h1)) ;; This is kinda ugly -- just for tracing.
     (when (null (h1))
	   (break "
***
*** MAYBE MSSING DEFINITION FROM THIS CALL: ~s
***
" (caadr (h1+))))
     (when (stringp (h1))
       (ipl-trace :run "~%At INTERPRET-Q: H1 = ~s, de-referencing!~%" (h1))
       (setf (h1) (*val+ (h1)))
       (go INTERPRET-Q))
     (when (functionp (h1))
       (ipl-trace :run-full ">> Calling Built-in ~a~%" trace-name-temp) 
       (funcall (h1) (h0) (second (h0+))) ;; Call the fn
       (pop (h1+)) ;; Remove the JFn call
       (go ADVANCE)
       )
     (ipl-trace :run "~%H1 = ~s!~%" (h1))
     (setq card (first (h1)))
     (ipl-trace :cards "Executing card: ~s~%" card)
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
     (ipl-trace :run " w/Q = ~s, symb=~s~%" q symb)
     (case q
       (0 (setf (s) symb) (go INTERPRET-P))
       (1 (setf (s) (*val symb)) (go INTERPRET-P))
       (2 (setf (s) (*val (*val symb))) (go INTERPRET-P))
       (3 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" card) (setf (s) symb) (go INTERPRET-P))
       (4 (format t "UNIMPLEMENTED MONITOR ACTION IN ~%~s~% -- CONTINUING!" card) (setf (s) symb) (go INTERPRET-P))
       (5 (call-ipl-prim symb) (go ASCEND)) ;; ??? THIS IS VERY UNCLEAR; NO PUSH ???
       (6 (error "In RUN at INTERPRET-Q:~%~s~%, Q=6 unimplmented!" card))
       (7 (error "In RUN at INTERPRET-Q:~%~s~%, Q=7 unimplmented!" card))
       )
   INTERPRET-P (ipl-trace :run-full "*** INTERPRET-P")
     (ipl-trace :run "INTERPRET-P w/P = ~s, symb=~s~%" p symb)
     ;; - P = 0: Go to TEST FOR PRIMITIVE. - P=1, 2, 3, 4, 5, 6: Perform the
     ;; - operation; go to  ADVANCE. - P = 7: Go to BRANCH.
     (case p
       (0 (go TEST-FOR-PRIMITIVE))
       (1 ;; Input S (after preserving HO) ;; ??? Hopefully "input" means to push it on the stack ???
	(push (s) (h0+))
	)
       (2 ;; Output to S (then restore HO)
	(setf (s) (pop (h0+))))
       (3 ;; Restore (pop up) S 
	(pop (s+)))
       (4 ;; Preserve (push down) S
	(push (s) (s+)))
       (5 ;; Replace (0) by S
	(setf (h0) (s)))
       (6 ;; Copy (0) in S ;; ??? Is this just moving H0 to S or to what S points to?
	(setf (symval s) (h0)))
       (7 ;; Branch to S if H5-
	(go BRANCH)) ;;; ??? WWW The 3.15 and cheat sheet slightly disagree on this ??? WWW
       )
     (go ADVANCE)
   TEST-FOR-PRIMITIVE (ipl-trace :run-full "*** TEST-FOR-PRIMITIVE")
     ;; Q of S: - Q = 5: Transfer machine control to SYMB of S (executing
     ;; primitive); go to ADVANCE. - Q ~= 5: Go to DESCEND
     (ipl-trace :run "At TEST-FOR-PRIMITIVE w/S = ~s, Q = ~a, symb=~s~%" (s) q symb)
     (case q 
       (5 (setf link (card-symb scard??????????)) (go ADVANCE))
       (t (go DESCEND)))
   ADVANCE (ipl-trace :run-full "*** ADVANCE")
     (when (equal (h1) :exit)
       (ipl-trace :run "Exiting from IPL-EVAL ^^^^^^^^^^^^^^^")
       (pop (h1+))
       (return))
     ;; Interpret LINK: - LINK= 0: Termination; go to ASCEND. LINK ~= 0: LINK is
     ;; the name of the cell containing the next instruction; put LINK in H1; go
     ;; to INTERPRET-Q.
     (setf link (card-link card))
     (ipl-trace :run "At ADVANCE w/LINK = ~a~%" link)
     ;; If link is nil ("") in the middle of a function, go next card, else ascend.
     (if (string-equal link "")
	 (if (null (h1))
	     (go ASCEND)
	     (progn (pop (h1)) 
		    (go INTERPRET-Q)))
	 (progn
	   (setf (h1) link)
	   (go INTERPRET-Q)))
     ;; FFF ASCEND and DESCEND could probably be handled more cleanly and
     ;; correctly by recursing on IPL-EVAL !!!
   ASCEND (ipl-trace :run-full "*** ASCEND")
     ;; Restore H1 (returning to H1 the name of the cell holding the current
     ;; instruction, one level up); restore auxiliary region if required (not!);
     ;; go to ADVANCE.
     (pop (h1+))
     (ipl-trace :run "At ASCEND w/H1 = ~a~%" (h1))
     (go ADVANCE)
   DESCEND (ipl-trace :run-full "*** DESCEND")
     (ipl-trace :run "At DESCEND w/S = ~a~%" (s))
     ;; Preserve H1: Put S into H1 (H1 now contains the name of the cell holding
     ;; the first instruction of the subprogram list); go to INTERPRET-Q.
     (push (s) (h1+))
     (go INTERPRET-Q)
   BRANCH (ipl-trace :run-full "*** BRANCH")
     (ipl-trace :run "At BRANCH w/H5 = ~a, S= ~a~%" (h5) (s))
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
(trace ipl-eval)
(setf *ipl-trace-list* '(:jfns :cards :io)) ;; :load :run :jfns :run-full :cards :io
(load-ipl "runs/20250214/LT.lisp")

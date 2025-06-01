(defstruct (cell (:print-function print-cell))
  (comments "")
  (type "")
  (name "") ;; This field is actually not a part of the cell and maybe shouldn't exist??? FFF
  (sign "")
  (pq "")
  (symb "")
  (link "")
  (comments.1 "")
  (id "")
  )

(defvar *jfn->name* (make-hash-table :test #'equal))
(clrhash *jfn->name*) ;; In case we're reloading

(defmacro defj (name args explanation &rest forms)
  `(let ((uname ,(string-upcase (format nil "~a" name))))
     (setf (gethash uname *jfn-plists*) '(explanation ,explanation))
     (let ((fn (lambda ,args ,@forms)))
       (setf (gethash uname *symtab*) fn)
       (setf (gethash fn *jfn->name*) uname))))

  (defj J73 (arg0) "Copy list [186]"
	(let* ((new-cell
		(if (zero? arg0)
		    (let* ((new-cell (make-cell! :pq "00" :symb "0" :link "0")))
		      new-cell)
		    (copy-ipl-list-and-return-head arg0))))
	  (poph0 1)
	  (ipush "H0" (cell-name new-cell))))

  (defj J74 (arg0) "Copy List Structure [186]"
	(let* ((new-cell
		(if (zero? arg0)
		    (let* ((new-cell (make-cell! :pq "00" :symb "0" :link "0")))
		      new-cell)
		    (copy-ipl-list-and-return-head arg0))))
	  (poph0 1)
	  (ipush "H0" (cell-name new-cell))))

(defun copy-ipl-list-and-return-head (head)
  (setf *copy-list-head-collector* nil)
  (copy-ipl-list (cell head) head)
  *copy-list-head-collector*
 )

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


=======================
;;; IPL-V List Copying Functions (Updated to Handle Q=2 Local Symbols)

;; In IPL-V, the Q=2 designation used to mark a symbol as "local" does not modify the symbol itself
;; or the cell it names. Instead, it is a property of the IPL word (cell) that contains the symbol in
;; its SYMB field. When the Q field of such a word is set to 2, it signals to the loader or copier
;; (e.g., during J74) that the symbol should be treated as local—meaning it will be replaced with a
;; newly generated, unique name. This ensures the symbol is localized to the copied context and avoids
;; naming collisions. This behavior is described explicitly on:
;;   - Page 200, under J136: "The output (0) is the input (0) with Q = 2..."
;;   - Page 148: "If the SYMB field of a word is marked with Q=2, the loader recognizes it as a local symbol."
;;   - Page 29: "To create a local symbol... set Q=2 in the cell in which the name appears."

(defvar *remap* (make-hash-table :test 'eq))

(defun q2-symbol-p (cell)
  "Returns T if the cell has Q=2 and a symbol in SYMB."
  (and (symbolp (symb cell)) (= (q cell) 2)))

(defun remap-symbol (symbol)
  "Return remapped symbol if present; otherwise return symbol."
  (gethash symbol *remap* symbol))

(defun find-or-create-local-symbol (symbol)
  (or (gethash symbol *remap*)
      (setf (gethash symbol *remap*) (newsym))))

(defun copy-cell (cell)
  "Shallow copy of a single IPL word, remapping Q=2 symbols."
  (let* ((new-cell (make-word))
         (sym (symb cell))
         (qval (q cell))
         (new-sym (if (and (symbolp sym) (= qval 2))
                      (find-or-create-local-symbol sym)
                      sym)))
    (setf (symb new-cell) new-sym
          (q new-cell) 0 ;; copied symbols are naked
          (p new-cell) (p cell)
          (link new-cell) nil)
    new-cell))

(defun walk-list (head)
  "Return a list of cells from HEAD to the end of the LINK chain."
  (let (result)
    (loop while head do
      (push head result)
      (setf head (link head)))
    (nreverse result)))

(defun list-header-p (sym)
  "Returns T if SYM names a valid IPL-V list header cell."
  (let ((cell (get-cell sym)))
    (and cell (link cell))))

(DEFJ J73 (args)
  "Shallow copy of list (J73)."
  (clrhash *remap*)
  (let* ((original (car args))
         (copy-head nil)
         (copy-tail nil))
    (dolist (cell (walk-list original))
      (let ((copy (copy-cell cell)))
        (when copy-tail
          (setf (link copy-tail) copy))
        (unless copy-head (setf copy-head copy))
        (setf copy-tail copy)))
    copy-head))

(defun copy-structure-rec (cell)
  "Recursively copy structure rooted at CELL, respecting Q=2."
  (when (null cell) (return-from copy-structure-rec nil))
  (let* ((copy (copy-cell cell))
         (sym (symb cell)))
    ;; If SYMB points to a list, copy it too
    (when (list-header-p sym)
      (setf (symb copy) (copy-structure-rec (get-cell sym))))
    ;; Recurse on link
    (setf (link copy) (copy-structure-rec (link cell)))
    copy))

(DEFJ J74 (args)
  "Deep structure copy (J74)."
  (clrhash *remap*)
  (let ((original (car args)))
    (copy-structure-rec original)))

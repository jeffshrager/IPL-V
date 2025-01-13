;; List Processing Operations (J60-J104)

;; Utility functions
(defun get-link (cell)
  "Get the link value, handling termination symbols"
  (let ((link (ipl-cell-link cell)))
    (if (zerop link) nil link)))

(defun set-termination (cell)
  "Set cell as termination cell"
  (setf (ipl-cell-link cell) 0))

;; J60: Locate next symbol after cell (0)
(defun j60 ()
  (let* ((cell-addr (ipl-cell-symb *H0*))
         (cell (get-cell cell-addr))
         (next-addr (get-link cell)))
    (if next-addr
        (progn
          (push-ho next-addr)
          (setf *H5* '+))
        (progn
          (push-ho cell-addr)
          (setf *H5* '-)))))

;; J61: Locate last symbol on list (0)
(defun j61 ()
  (let ((curr-addr (ipl-cell-symb *H0*)))
    (loop for cell = (get-cell curr-addr)
          for next = (get-link cell)
          while next
          do (setf curr-addr next)
          finally (progn
                   (push-ho curr-addr)
                   (setf *H5* '+)))))

;; J62: Locate (0) on list (1) - first occurrence
(defun j62 ()
  (let* ((target (pop-ho))
         (list-addr (ipl-cell-symb *H0*))
         (found nil))
    (loop for curr-addr = list-addr then (get-link (get-cell curr-addr))
          while (and curr-addr (not found))
          do (let ((cell (get-cell curr-addr)))
               (when (equal (ipl-cell-symb cell) target)
                 (setf found curr-addr)))
          finally (progn
                   (push-ho (or found list-addr))
                   (setf *H5* (if found '+ '-))))))

;; J63, J64: Insert symbol before/after cell
(defun create-list-cell (symb link)
  "Create a new list cell with given symbol and link"
  (let ((addr (allocate-cell)))
    (set-cell addr (make-ipl-cell :symb symb :link link))
    addr))

(defun j63 ()
  (let* ((new-symb (pop-ho))
         (cell-addr (ipl-cell-symb *H0*))
         (cell (get-cell cell-addr))
         (old-symb (ipl-cell-symb cell))
         (next-addr (ipl-cell-link cell)))
    (setf (ipl-cell-symb cell) new-symb)
    (create-list-cell old-symb next-addr)))

(defun j64 ()
  (let* ((new-symb (pop-ho))
         (cell-addr (ipl-cell-symb *H0*))
         (cell (get-cell cell-addr))
         (next-addr (ipl-cell-link cell)))
    (let ((new-addr (create-list-cell new-symb next-addr)))
      (setf (ipl-cell-link cell) new-addr))))

;; J65: Insert (0) at end of list (1)
(defun j65 ()
  (let* ((symb (pop-ho))
         (list-addr (ipl-cell-symb *H0*)))
    (j61)  ; locate last cell
    (let ((last-addr (ipl-cell-symb *H0*)))
      (let ((new-addr (create-list-cell symb 0)))
        (setf (ipl-cell-link (get-cell last-addr)) new-addr)))))

;; List Structure Management
(defun make-empty-list ()
  "Create an empty list (just head cell)"
  (let ((addr (allocate-cell)))
    (set-cell addr (make-ipl-cell))
    (set-termination (get-cell addr))
    addr))

;; J71: Erase list (0)
(defun j71 ()
  (let ((list-addr (ipl-cell-symb *H0*)))
    (loop for curr-addr = list-addr then next
          for cell = (get-cell curr-addr)
          for next = (get-link cell)
          do (remhash curr-addr *memory*)
          while next)))

;; J72: Erase list structure (0)
(defun local-symbol-p (symb)
  "Test if symbol is local (starts with 9-)"
  (and (stringp symb)
       (> (length symb) 2)
       (string= (subseq symb 0 2) "9-")))

(defun j72 ()
  (labels ((erase-structure (addr)
             (when addr
               (let* ((cell (get-cell addr))
                      (symb (ipl-cell-symb cell))
                      (next (get-link cell)))
                 (when (local-symbol-p symb)
                   (erase-structure symb))
                 (remhash addr *memory*)
                 (when next
                   (erase-structure next))))))
    (erase-structure (ipl-cell-symb *H0*))))

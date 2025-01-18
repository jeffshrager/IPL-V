;; Data Term and Arithmetic Processes (J110-J129)

;; Data term structure
(defstruct (data-term (:predicate data-term?))
  type    ; 0=integer, 1=float, 2=alphanumeric, 3=octal
  value)  ; Actual value

(defun data-term-p (cell)
  "Test if cell contains a data term"
  (= (ipl-cell-q cell) 1))

(defun get-data-term (addr)
  "Get data term from cell"
  (let ((cell (get-cell addr)))
    (when (data-term-p cell)
      (ipl-cell-symb cell))))

;; Arithmetic Operations
(defun coerce-to-float (term)
  "Convert data term to floating point if needed"
  (let ((val (data-term-value term)))
    (if (integerp val)
        (float val)
        val)))

(defun arithmetic-result (val type)
  "Create arithmetic result data term"
  (make-data-term :type type
                  :value (if (= type 0)
                           (round val)
                           (float val))))

;; J110: Add (1) + (2) → (0)
(defun j110 ()
  (let* ((term2 (get-data-term (pop-ho)))
         (term1 (get-data-term (pop-ho)))
         (result-addr (ipl-cell-symb *H0*))
         (float-op (or (= (data-term-type term1) 1)
                      (= (data-term-type term2) 1)))
         (val (+ (if float-op 
                    (coerce-to-float term1)
                    (data-term-value term1))
                (if float-op
                    (coerce-to-float term2)
                    (data-term-value term2))))
         (result (arithmetic-result val (if float-op 1 0))))
    (set-cell result-addr 
              (make-ipl-cell :q 1 
                            :symb result))))

;; J114: Test if (0) = (1)
(defun j114 ()
  (let* ((term1 (get-data-term (pop-ho)))
         (term0 (get-data-term (ipl-cell-symb *H0*))))
    (setf *H5* (if (and (= (data-term-type term0)
                          (data-term-type term1))
                       (= (data-term-value term0)
                          (data-term-value term1)))
                   '+
                   '-))))

;; J124: Clear (0)
(defun j124 ()
  (let ((addr (ipl-cell-symb *H0*)))
    (set-cell addr
              (make-ipl-cell :q 1
                            :symb (make-data-term :type 0
                                                :value 0)))))

;; J125: Tally 1 in (0)
(defun j125 ()
  (let* ((addr (ipl-cell-symb *H0*))
         (term (get-data-term addr)))
    (set-cell addr
              (make-ipl-cell :q 1
                            :symb (make-data-term 
                                  :type (data-term-type term)
                                  :value (1+ (data-term-value term)))))))

;; Random number generation
(setf *random-state* (make-random-state t))

;; J129: Random number between 0 and (0)
(defun j129 ()
  (let* ((bound (data-term-value (get-data-term (ipl-cell-symb *H0*))))
         (val (random (float bound) *random-state*)))
    (push-ho (make-ipl-cell 
              :q 1
              :symb (make-data-term :type 1 :value val)))))

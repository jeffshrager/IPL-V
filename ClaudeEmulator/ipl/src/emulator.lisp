;; IPL-V Emulator in Common Lisp

;; Basic cell structure
(defstruct ipl-cell
  p      ; P prefix (0-7)
  q      ; Q prefix (0-7)
  symb   ; Symbol part
  link)  ; Link part

;; System cells
(defparameter *H0* (make-ipl-cell)) ; Communication cell
(defparameter *H1* (make-ipl-cell)) ; Current instruction address
(defparameter *H2* (make-ipl-cell)) ; Available space list
(defparameter *H3* 0)               ; Interpretation cycle count
(defparameter *H4* (make-ipl-cell)) ; Current auxiliary routine
(defparameter *H5* '+)              ; Test cell (+ or -)

;; Memory management
(defparameter *memory* (make-hash-table))
(defparameter *next-address* 1000)

(defun allocate-cell ()
  "Allocate a new cell from available space"
  (let ((addr *next-address*))
    (setf (gethash addr *memory*) (make-ipl-cell))
    (incf *next-address*)
    addr))

(defun get-cell (addr)
  "Get cell at given address"
  (gethash addr *memory*))

(defun set-cell (addr cell)
  "Set cell at given address"
  (setf (gethash addr *memory*) cell))

;; Basic instruction execution
(defun get-designated-symbol (instruction)
  "Get designated symbol S based on Q code"
  (let ((q (ipl-cell-q instruction))
        (symb (ipl-cell-symb instruction)))
    (case q
      (0 symb)  ; S = SYMB
      (1 (ipl-cell-symb (get-cell symb)))  ; S = symbol in cell named SYMB
      (2 (ipl-cell-symb  ; S = symbol in cell whose name is in cell named SYMB
          (get-cell 
           (ipl-cell-symb (get-cell symb)))))
      (otherwise symb))))  ; Q=3,4 treated as Q=0 for now

(defun execute-instruction (instruction)
  "Execute a single IPL instruction"
  (let* ((p (ipl-cell-p instruction))
         (s (get-designated-symbol instruction))
         (link (ipl-cell-link instruction)))
    (case p
      (0 (execute-routine s))          ; Execute S
      (1 (push-ho s))                  ; Input S
      (2 (store-output s))             ; Output to S
      (3 (restore-cell s))             ; Restore S
      (4 (preserve-cell s))            ; Preserve S
      (5 (replace-ho s))               ; Replace (0) by S
      (6 (copy-ho s))                  ; Copy (0) in S
      (7 (if (eq *H5* '-) s link)))    ; Branch to S if H5-
    link))

;; HO stack operations
(defvar *ho-stack* nil)

(defun push-ho (val)
  "Push value onto HO stack"
  (push val *ho-stack*)
  (setf (ipl-cell-symb *H0*) (car *ho-stack*)))

(defun pop-ho ()
  "Pop value from HO stack"
  (let ((val (pop *ho-stack*)))
    (setf (ipl-cell-symb *H0*) (car *ho-stack*))
    val))

;; Basic interpretation cycle
(defun interpret-step ()
  "Execute one interpretation cycle"
  (let* ((curr-addr (ipl-cell-symb *H1*))
         (instruction (get-cell curr-addr))
         (next-addr (execute-instruction instruction)))
    (incf *H3*)
    (setf (ipl-cell-symb *H1*) next-addr)
    next-addr))

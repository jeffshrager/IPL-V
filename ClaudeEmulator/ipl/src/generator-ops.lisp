;; Generator Operations (J17-J19)

(defstruct generator-context
  subprocess           ; Name of subprocess
  working-cells       ; List of cells being used
  state)              ; Additional state info

(defvar *generator-stack* nil)

;; J17: Generator Setup
(defun j17 ()
  (let* ((subprocess (pop-ho))
         (max-w (ipl-cell-symb *H0*))
         (context (make-generator-context
                  :subprocess subprocess
                  :working-cells (loop for i from 0 to max-w
                                     collect (cons i (get-cell (format nil "W~D" i)))))))
    (push context *generator-stack*)))

;; J18: Execute Subprocess
(defun j18 ()
  (let ((context (car *generator-stack*)))
    ;; Save current working cells
    (dolist (cell (generator-context-working-cells context))
      (push (get-cell (format nil "W~D" (car cell))) *ho-stack*))
    ;; Restore original working cells
    (dolist (cell (generator-context-working-cells context))
      (set-cell (format nil "W~D" (car cell)) (cdr cell)))
    ;; Execute subprocess
    (let ((subproc (generator-context-subprocess context)))
      (execute-routine subproc))
    ;; Restore generator working cells
    (dolist (cell (reverse (generator-context-working-cells context)))
      (let ((saved (pop *ho-stack*)))
        (set-cell (format nil "W~D" (car cell)) saved)))))

;; J19: Generator Cleanup
(defun j19 ()
  (let ((context (pop *generator-stack*)))
    ;; Restore original working cells
    (dolist (cell (generator-context-working-cells context))
      (set-cell (format nil "W~D" (car cell)) (cdr cell)))))

;; J100: Generate symbols from list
(defun j100 ()
  (let* ((subprocess (pop-ho))
         (list-addr (ipl-cell-symb *H0*)))
    (j17)  ; Setup generator
    (loop for curr-addr = list-addr then (get-link (get-cell curr-addr))
          while (and curr-addr (eq *H5* '+))
          do (push-ho (ipl-cell-symb (get-cell curr-addr)))
             (j18))  ; Execute subprocess
    (j19)))  ; Cleanup generator

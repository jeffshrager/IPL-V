;; Basic Print Operations

(defun print-data-term (term)
  (format t "~A" (data-term-value term)))

(defun print-cell (addr)
  (let ((cell (get-cell addr)))
    (cond 
      ((data-term-p cell)
       (print-data-term (ipl-cell-symb cell)))
      (t
       (format t "~A" (ipl-cell-symb cell))))))

;; J151: Print list (0)
(defun j151 ()
  (let ((list-addr (ipl-cell-symb *H0*)))
    (format t "~%List contents:~%")
    (loop for curr-addr = list-addr then (get-link (get-cell curr-addr))
          while curr-addr
          do (print-cell curr-addr)
             (format t "~%"))))

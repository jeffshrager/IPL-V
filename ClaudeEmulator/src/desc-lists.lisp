;; Description List Processes (J10-J16)

(defun get-description-list (list-addr)
  "Get the description list of a list (from head)"
  (let ((head-cell (get-cell list-addr)))
    (ipl-cell-symb head-cell)))

(defun set-description-list (list-addr desc-list-addr)
  "Set the description list of a list (in head)"
  (let ((head-cell (get-cell list-addr)))
    (setf (ipl-cell-symb head-cell) desc-list-addr)))

;; J10: Find value of attribute (0) on description list of (1)
(defun j10 ()
  (let* ((attr (pop-ho))
         (list-addr (ipl-cell-symb *H0*))
         (desc-list (get-description-list list-addr)))
    (if (not desc-list)
        (setf *H5* '-)
        (loop for curr-addr = desc-list then (get-link (get-cell curr-addr))
              while curr-addr
              for cell = (get-cell curr-addr)
              for next = (get-link cell)
              when (equal (ipl-cell-symb cell) attr)
                do (progn
                     (push-ho (ipl-cell-symb (get-cell next)))
                     (setf *H5* '+)
                     (return))
              finally (setf *H5* '-)))))

;; J11: Assign value (1) to attribute (0) on list (2)
(defun j11 ()
  (let* ((value (pop-ho))
         (attr (pop-ho))
         (list-addr (ipl-cell-symb *H0*))
         (desc-list (get-description-list list-addr)))
    ;; Create description list if it doesn't exist
    (unless desc-list
      (setf desc-list (make-empty-list))
      (set-description-list list-addr desc-list))
    ;; Remove existing attribute-value pair if present
    (loop for curr-addr = desc-list then (get-link (get-cell curr-addr))
          while curr-addr
          for cell = (get-cell curr-addr)
          for next = (get-link cell)
          when (equal (ipl-cell-symb cell) attr)
            do (progn
                 (setf (ipl-cell-link cell) 
                       (get-link (get-cell next)))
                 (remhash next *memory*)))
    ;; Add new attribute-value pair at front
    (let* ((value-addr (create-list-cell value (get-link (get-cell desc-list))))
           (attr-addr (create-list-cell attr value-addr)))
      (setf (ipl-cell-link (get-cell desc-list)) attr-addr))))

;; J14: Erase attribute (0) from list (1)
(defun j14 ()
  (let* ((attr (pop-ho))
         (list-addr (ipl-cell-symb *H0*))
         (desc-list (get-description-list list-addr)))
    (when desc-list
      (loop for curr-addr = desc-list then (get-link (get-cell curr-addr))
            while curr-addr
            for cell = (get-cell curr-addr)
            for next = (get-link cell)
            when (equal (ipl-cell-symb cell) attr)
              do (progn
                   (setf (ipl-cell-link cell) 
                         (get-link (get-cell next)))
                   (remhash next *memory*))))))

;; J15: Erase all attributes of (0)
(defun j15 ()
  (let* ((list-addr (ipl-cell-symb *H0*))
         (desc-list (get-description-list list-addr)))
    (when desc-list
      (j71)  ; Erase the description list
      (set-description-list list-addr nil))))

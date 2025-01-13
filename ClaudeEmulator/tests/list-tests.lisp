;; tests/list-tests.lisp

(in-package :ipl/tests)

(def-suite ipl-list-tests
  :description "Tests for list processing operations")

(in-suite ipl-list-tests)

(defun make-test-list (items)
  "Create a test list with given items"
  (let* ((head-addr (allocate-cell))
         (curr-addr head-addr))
    (set-cell head-addr (make-ipl-cell))
    (dolist (item items)
      (let ((next-addr (allocate-cell)))
        (set-cell curr-addr 
                  (make-ipl-cell :symb (car item)
                                :link (if (cdr item) next-addr 0)))
        (setf curr-addr next-addr)))
    head-addr))

(test list-navigation
  "Test J60 and J61 for list navigation"
  (let ((list-addr (make-test-list '((A . t) (B . t) (C . nil)))))
    ;; Test J60 - Locate next
    (setf (ipl-cell-symb *h0*) list-addr)
    (j60)
    (is (eq *h5* '+))
    (let ((cell (get-cell (ipl-cell-symb *h0*))))
      (is (eq (ipl-cell-symb cell) 'A)))
    
    ;; Test J61 - Locate last
    (setf (ipl-cell-symb *h0*) list-addr)
    (j61)
    (is (eq *h5* '+))
    (let ((cell (get-cell (ipl-cell-symb *h0*))))
      (is (eq (ipl-cell-symb cell) 'C)))))

(test list-insertion
  "Test J64 and J65 for list insertion"
  (let ((list-addr (make-test-list '((A . t) (B . nil)))))
    ;; Test J64 - Insert after
    (setf (ipl-cell-symb *h0*) list-addr)
    (j60)  ; Move to first cell
    (push-ho 'X)
    (j64)
    (setf (ipl-cell-symb *h0*) list-addr)
    (j61)  ; Go to last cell
    (let ((cell (get-cell (ipl-cell-symb *h0*))))
      (is (eq (ipl-cell-symb cell) 'B)))
    
    ;; Test J65 - Insert at end
    (push-ho 'Y)
    (push-ho list-addr)
    (j65)
    (setf (ipl-cell-symb *h0*) list-addr)
    (j61)
    (let ((cell (get-cell (ipl-cell-symb *h0*))))
      (is (eq (ipl-cell-symb cell) 'Y)))))

(test list-deletion
  "Test J71 for list erasure"
  (let ((list-addr (make-test-list '((A . t) (B . nil)))))
    (push-ho list-addr)
    (j71)
    (is (null (get-cell list-addr)))))

(test list-searching
  "Test J77 for symbol searching"
  (let ((list-addr (make-test-list '((A . t) (B . t) (C . nil)))))
    ;; Test finding existing symbol
    (push-ho 'B)
    (push-ho list-addr)
    (j77)
    (is (eq *h5* '+))
    
    ;; Test finding non-existent symbol
    (push-ho 'X)
    (push-ho list-addr)
    (j77)
    (is (eq *h5* '-))))

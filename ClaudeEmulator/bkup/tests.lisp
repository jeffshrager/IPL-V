;; tests/core-tests.lisp - Basic tests for IPL-V emulator

(in-package :ipl/tests)

(def-suite ipl-core-tests
  :description "Core functionality tests for IPL-V emulator")

(in-suite ipl-core-tests)

(test cell-creation
  "Test basic cell creation and manipulation"
  (let ((cell (make-ipl-cell :p 1 :q 2 :symb 'test :link 100)))
    (is (= (ipl-cell-p cell) 1))
    (is (= (ipl-cell-q cell) 2))
    (is (eq (ipl-cell-symb cell) 'test))
    (is (= (ipl-cell-link cell) 100))))

(test memory-operations
  "Test memory allocation and access"
  (let ((addr (allocate-cell)))
    (is (integerp addr))
    (let ((cell (make-ipl-cell :symb 'test)))
      (set-cell addr cell)
      (is (equalp (get-cell addr) cell)))))

(test basic-instruction
  "Test basic instruction execution"
  (let* ((addr1 (allocate-cell))
         (addr2 (allocate-cell)))
    ;; Create a simple instruction: input symbol
    (set-cell addr1 
              (make-ipl-cell :p 1 :q 0 :symb 'test :link addr2))
    ;; Set H1 to point to our instruction
    (setf (ipl-cell-symb *h1*) addr1)
    ;; Execute one step
    (interpret-step)
    ;; Check that symbol was input to H0
    (is (eq (ipl-cell-symb *h0*) 'test))))

(test list-operations
  "Test basic list operations"
  ;; Create a list with two elements
  (let* ((list-addr (allocate-cell))
         (cell1 (allocate-cell))
         (cell2 (allocate-cell)))
    (set-cell list-addr (make-ipl-cell :link cell1))
    (set-cell cell1 (make-ipl-cell :symb 'item1 :link cell2))
    (set-cell cell2 (make-ipl-cell :symb 'item2 :link 0))
    
    ;; Test J60 (locate next)
    (setf (ipl-cell-symb *h0*) list-addr)
    (j60)
    (is (eq *h5* '+))
    (is (= (ipl-cell-symb *h0*) cell1))
    
    ;; Test J61 (locate last)
    (setf (ipl-cell-symb *h0*) list-addr)
    (j61)
    (is (eq *h5* '+))
    (is (= (ipl-cell-symb *h0*) cell2))))

(test arithmetic-operations
  "Test arithmetic operations"
  ;; Create two data terms
  (let* ((dt1-addr (allocate-cell))
         (dt2-addr (allocate-cell))
         (result-addr (allocate-cell)))
    (set-cell dt1-addr 
              (make-ipl-cell :q 1 
                            :symb (make-data-term :type 0 
                                                :value 10)))
    (set-cell dt2-addr 
              (make-ipl-cell :q 1 
                            :symb (make-data-term :type 0 
                                                :value 20)))
    ;; Test addition
    (push-ho dt1-addr)
    (push-ho dt2-addr)
    (setf (ipl-cell-symb *h0*) result-addr)
    (j110)
    (let ((result (get-data-term result-addr)))
      (is (= (data-term-value result) 30)))))

(defun run-tests ()
  (run! 'ipl-core-tests))

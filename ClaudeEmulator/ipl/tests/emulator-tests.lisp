;; tests/emulator-tests.lisp

(in-package :ipl/tests)

(def-suite ipl-emulator-tests
  :description "Core emulator functionality tests")

(in-suite ipl-emulator-tests)

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

(test basic-instruction-execution
  "Test basic instruction execution"
  (let* ((addr1 (allocate-cell))
         (addr2 (allocate-cell)))
    ;; Create a simple input instruction
    (set-cell addr1 
              (make-ipl-cell :p 1 :q 0 :symb 'test :link addr2))
    (setf (ipl-cell-symb *h1*) addr1)
    (interpret-step)
    (is (eq (ipl-cell-symb *h0*) 'test))))

(test stack-operations
  "Test HO stack operations"
  (push-ho 'first)
  (push-ho 'second)
  (is (eq (ipl-cell-symb *h0*) 'second))
  (pop-ho)
  (is (eq (ipl-cell-symb *h0*) 'first)))

(test data-term-operations
  "Test data term handling"
  (let ((dt (make-data-term :type 0 :value 42)))
    (is (= (data-term-value dt) 42))
    (is (= (data-term-type dt) 0))))

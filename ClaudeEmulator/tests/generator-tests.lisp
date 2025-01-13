;; tests/generator-tests.lisp

(in-package :ipl/tests)

(def-suite ipl-generator-tests
  :description "Tests for generator operations")

(in-suite ipl-generator-tests)

;; Helper subprocess that collects generated items
(defvar *collected-items* nil)

(defun collector-subprocess ()
  (push (ipl-cell-symb *h0*) *collected-items*)
  (setf *h5* '+))

(test generator-setup-cleanup
  "Test J17 and J19 generator setup/cleanup"
  (let ((orig-val 'original)
        (subprocess 'test-process))
    ;; Set up initial state
    (set-cell "W0" (make-ipl-cell :symb orig-val))
    
    ;; Test generator setup
    (push-ho 'W0)
    (push-ho subprocess)
    (j17)
    (is (= (length *generator-stack*) 1))
    (let ((context (car *generator-stack*)))
      (is (eq (generator-context-subprocess context) subprocess)))
    
    ;; Test cleanup
    (j19)
    (is (= (length *generator-stack*) 0))
    (let ((final-cell (get-cell "W0")))
      (is (eq (ipl-cell-symb final-cell) orig-val)))))

(test basic-generation
  "Test J100 list symbol generation"
  (let ((list-addr (make-test-list '((A . t) (B . t) (C . nil)))))
    (setf *collected-items* nil)
    
    ;; Create and run generator
    (push-ho list-addr)
    (push-ho 'collector-subprocess)
    (j100)
    
    ;; Check collected items
    (is (equal (reverse *collected-items*) '(A B C)))))

(test generator-early-termination
  "Test generator termination via subprocess"
  (let ((list-addr (make-test-list '((A . t) (B . t) (C . t) (D . nil))))
        (*collected-items* nil))
    
    ;; Define subprocess that stops after B
    (flet ((stopping-subprocess ()
             (let ((item (ipl-cell-symb *h0*)))
               (push item *collected-items*)
               (setf *h5* (if (eq item 'B) '- '+)))))
      
      ;; Run generator
      (push-ho list-addr)
      (push-ho #'stopping-subprocess)
      (j100)
      
      ;; Check only items before stop point were collected
      (is (equal (reverse *collected-items*) '(A B))))))

(test nested-generators
  "Test nested generator operation"
  (let ((outer-list (make-test-list '((A . t) (B . nil))))
        (inner-list (make-test-list '((1 . t) (2 . nil))))
        (*collected-items* nil))
    
    ;; Define outer subprocess that generates inner list
    (flet ((outer-subprocess ()
             (push-ho inner-list)
             (push-ho 'collector-subprocess)
             (j100)
             (setf *h5* '+)))
      
      ;; Run outer generator
      (push-ho outer-list)
      (push-ho #'outer-subprocess)
      (j100)
      
      ;; Check all items were collected
      (is (equal (length *collected-items*) 4))
      (is (subsetp '(1 2) *collected-items*)))))

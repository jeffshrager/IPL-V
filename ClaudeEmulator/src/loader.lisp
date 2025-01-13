;; Program Loading and Running

(defun parse-ipl-instruction (name p q symb link)
  "Create an IPL instruction cell from components"
  (let ((addr (or (parse-integer name :junk-allowed t) 
                  (allocate-cell))))
    (set-cell addr 
              (make-ipl-cell 
               :p (or p 0)
               :q (or q 0)
               :symb symb
               :link (or link 0)))
    addr))

(defun load-ipl-program (instructions)
  "Load a sequence of IPL instructions into memory"
  (let ((start-addr nil))
    (dolist (inst instructions)
      (let ((addr (apply #'parse-ipl-instruction inst)))
        (unless start-addr (setq start-addr addr))))
    start-addr))

(defun run-ipl-program (start-addr &key (max-cycles 1000))
  "Run an IPL program from given start address"
  (setf (ipl-cell-symb *H1*) start-addr)
  (setf *H3* 0)
  (loop while (and (ipl-cell-symb *H1*)
                   (< *H3* max-cycles))
        do (interpret-step)
        collect (list :cycles *H3*
                     :h0 (ipl-cell-symb *H0*)
                     :h5 *H5*)))

;; Test program: Create a list, add some numbers, sum them
(defvar *test-program*
  '(;; NAME  P Q SYMB LINK
    ("R1"   0 0 "J90" "9-1")    ; Create new list
    ("9-1"  2 0 "W0"  "9-2")    ; Store list addr in W0
    ("9-2"  1 0 "N1"  "9-3")    ; Input first number (data term)
    ("9-3"  1 1 "W0"  "9-4")    ; Input list name
    ("9-4"  0 0 "J65" "9-5")    ; Add to end of list
    ("9-5"  1 0 "N2"  "9-6")    ; Input second number
    ("9-6"  1 1 "W0"  "9-7")    ; Input list name
    ("9-7"  0 0 "J65" "9-8")    ; Add to end of list
    ("9-8"  1 0 "N3"  "9-9")    ; Input third number
    ("9-9"  1 1 "W0"  "9-10")   ; Input list name
    ("9-10" 0 0 "J65" "9-11")   ; Add to end of list
    ("9-11" 1 1 "W0"  "9-12")   ; Input list name for printing
    ("9-12" 0 0 "J151" 0)))     ; Print list and terminate

;; Setup test data terms
(defun setup-test-data ()
  (parse-ipl-instruction "N1" 0 1 
                        (make-data-term :type 0 :value 10) 0)
  (parse-ipl-instruction "N2" 0 1 
                        (make-data-term :type 0 :value 20) 0)
  (parse-ipl-instruction "N3" 0 1 
                        (make-data-term :type 0 :value 30) 0))

;; Run the test
(defun run-test ()
  (clrhash *memory*)
  (setf *next-address* 1000)
  (setf *ho-stack* nil)
  (setup-test-data)
  (let ((start-addr (load-ipl-program *test-program*)))
    (format t "~%Starting IPL program execution...~%")
    (let ((trace (run-ipl-program start-addr)))
      (format t "~%Execution complete in ~A cycles~%" *H3*)
      (format t "Final H5: ~A~%" *H5*)
      trace)))

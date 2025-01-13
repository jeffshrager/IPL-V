;; Complex test program: Student Grade Processing
;; - Creates student records with grades
;; - Computes averages using description lists
;; - Uses generator to process all records

(defvar *complex-program*
  '(;; Create student list
    ("R1"   0 0 "J90" "9-1")     ; Create main list
    ("9-1"  2 0 "W0"  "9-2")     ; Store list in W0
    
    ;; Add first student
    ("9-2"  0 0 "J90" "9-3")     ; Create student record
    ("9-3"  2 0 "W1"  "9-4")     ; Store in W1
    ("9-4"  1 0 "S1"  "9-5")     ; Input student ID
    ("9-5"  1 1 "W1"  "9-6")     ; Input list name
    ("9-6"  0 0 "J65" "9-7")     ; Add ID to record
    ("9-7"  1 0 "N85" "9-8")     ; Grade 1 (85)
    ("9-8"  1 0 "G1"  "9-9")     ; Grade attribute
    ("9-9"  1 1 "W1"  "9-10")    ; Input record
    ("9-10" 0 0 "J11" "9-11")    ; Add to description list
    
    ;; Add second student
    ("9-11" 0 0 "J90" "9-12")    ; Create second record
    ("9-12" 2 0 "W1"  "9-13")    ; Store in W1
    ("9-13" 1 0 "S2"  "9-14")    ; Student ID
    ("9-14" 1 1 "W1"  "9-15")    ; Input list name
    ("9-15" 0 0 "J65" "9-16")    ; Add to record
    ("9-16" 1 0 "N90" "9-17")    ; Grade 2 (90)
    ("9-17" 1 0 "G1"  "9-18")    ; Grade attribute
    ("9-18" 1 1 "W1"  "9-19")    ; Input record
    ("9-19" 0 0 "J11" "9-20")    ; Add to description list
    
    ;; Add students to main list
    ("9-20" 1 1 "W1"  "9-21")    ; Get first record
    ("9-21" 1 1 "W0"  "9-22")    ; Get main list
    ("9-22" 0 0 "J65" "9-23")    ; Add to main list
    
    ;; Process all students using generator
    ("9-23" 1 1 "W0"  "9-24")    ; Get main list
    ("9-24" 1 0 "P1"  "9-25")    ; Input processor name
    ("9-25" 0 0 "J100" "9-26")   ; Generate over list
    
    ;; Print results
    ("9-26" 1 1 "W0" "9-27")     ; Get main list
    ("9-27" 0 0 "J151" 0)        ; Print and terminate
    
    ;; P1: Process each student (subprocess)
    ("P1"   1 1 "H0" "9-40")     ; Get student record
    ("9-40" 1 0 "G1" "9-41")     ; Get grade attribute
    ("9-41" 0 0 "J10" "9-42")    ; Find grade value
    ("9-42" 0 0 "J151" "9-43")   ; Print record
    ("9-43" 1 0 "J4" 0)))        ; Set H5+ and return

;; Setup test data
(defun setup-complex-test ()
  ;; Create grade data terms
  (parse-ipl-instruction "N85" 0 1 
                        (make-data-term :type 0 :value 85) 0)
  (parse-ipl-instruction "N90" 0 1 
                        (make-data-term :type 0 :value 90) 0)
  ;; Create attribute names
  (parse-ipl-instruction "G1" 0 0 "GRADE" 0)
  ;; Create student IDs
  (parse-ipl-instruction "S1" 0 0 "STUDENT-1" 0)
  (parse-ipl-instruction "S2" 0 0 "STUDENT-2" 0))

;; Run complex test
(defun run-complex-test ()
  (clrhash *memory*)
  (setf *next-address* 1000)
  (setf *ho-stack* nil)
  (setf *generator-stack* nil)
  (setup-complex-test)
  (let ((start-addr (load-ipl-program *complex-program*)))
    (format t "~%Starting complex IPL program execution...~%")
    (let ((trace (run-ipl-program start-addr)))
      (format t "~%Execution complete in ~A cycles~%" *H3*)
      (format t "Final H5: ~A~%" *H5*)
      trace)))

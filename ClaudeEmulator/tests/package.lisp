;; src/package.lisp - Package definition for IPL-V emulator

(defpackage :ipl
  (:use :cl :alexandria)
  (:export
   ;; Core structures
   #:ipl-cell
   #:make-ipl-cell
   #:ipl-cell-p
   #:ipl-cell-q
   #:ipl-cell-symb
   #:ipl-cell-link
   
   ;; System cells
   #:*h0*
   #:*h1*
   #:*h2*
   #:*h3*
   #:*h4*
   #:*h5*
   
   ;; Memory management
   #:allocate-cell
   #:get-cell
   #:set-cell
   
   ;; Basic operations
   #:execute-instruction
   #:interpret-step
   
   ;; List operations
   #:j60  ; Locate next
   #:j61  ; Locate last
   #:j62  ; Locate symbol
   #:j63  ; Insert before
   #:j64  ; Insert after
   #:j65  ; Insert at end
   #:j71  ; Erase list
   #:j72  ; Erase structure
   
   ;; Description list operations
   #:j10  ; Find value
   #:j11  ; Assign value
   #:j14  ; Erase attribute
   #:j15  ; Erase all attributes
   
   ;; Generator operations
   #:j17  ; Generator setup
   #:j18  ; Execute subprocess
   #:j19  ; Generator cleanup
   #:j100 ; Generate symbols
   
   ;; Arithmetic operations
   #:j110 ; Add
   #:j111 ; Subtract
   #:j114 ; Test equal
   #:j124 ; Clear
   #:j125 ; Tally
   
   ;; Program loading/running
   #:load-ipl-program
   #:run-ipl-program
   
   ;; Utilities
   #:reset-ipl-system
   #:run-test
   #:run-complex-test))

(defpackage :ipl/tests
  (:use :cl :ipl :fiveam)
  (:export #:run-tests))

;; ipl.asd - System definition for IPL-V emulator

(asdf:defsystem "ipl"
  :description "IPL-V Programming Language Emulator"
  :version "0.1.0"
  :author "IPL-V Emulator Team"
  :license "MIT"
  :depends-on (:alexandria)
  :components
  ((:module "src"
    :components
    ((:file "package")
     (:file "emulator" :depends-on ("package"))
     (:file "list-ops" :depends-on ("emulator"))
     (:file "desc-lists" :depends-on ("list-ops"))
     (:file "arithmetic" :depends-on ("emulator"))
     (:file "generator-ops" :depends-on ("list-ops"))
     (:file "print" :depends-on ("emulator"))
     (:file "loader" :depends-on ("emulator"))
     (:file "complex-test" :depends-on ("generator-ops" "print")))))
  :in-order-to ((test-op (test-op "ipl/tests"))))

;; Test system definition
(asdf:defsystem "ipl/tests"
  :description "Test suite for IPL-V emulator"
  :depends-on ("ipl" "fiveam")
  :components
  ((:module "tests"
    :components
    ((:file "package")
     (:file "emulator-tests" :depends-on ("package"))
     (:file "list-tests" :depends-on ("package"))
     (:file "generator-tests" :depends-on ("package"))))))

;;; Run dmoews's Stefferud LT deck on ../iplv.lisp.
;;; Usage (from this directory):
;;;   sbcl --non-interactive --load run-lt.lisp > lt-stefferud-lisp.out
(load (compile-file "../iplv.lisp"))
(set-trace-mode :none)
(setf *j15-mode* :clear-dl)
(handler-bind ((error (lambda (e)
                        (format t "~%ERROR at cycle ~a: ~a~%" (h3-cycles) e)
                        (sb-debug:print-backtrace :count 8)
                        (sb-ext:exit :code 1))))
  (load-ipl "lt-stefferud-run.iplv" :adv-limit 100000000))

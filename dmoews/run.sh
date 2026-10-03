#!/bin/sh
# Run dmoews's Stefferud (1963) Logic Theorist deck on ../iplv.lisp and
# compare with Stefferud's printed output.
cd "$(dirname "$0")"
cat logic-theorist-1963-stefferud.iplv logic-theorist-1963-stefferud-input.txt > lt-stefferud-run.iplv
sbcl --non-interactive --load run-lt.lisp > lt-stefferud-lisp.out 2>&1
python3 compare.py logic-theorist-1963-stefferud-output.txt lt-stefferud-lisp.out

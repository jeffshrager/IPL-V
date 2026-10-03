# Stefferud's Logic Theorist (dmoews deck) on the Lisp IPL-V

This directory is a copy of <https://github.com/dmoews/ipl-v-logic-theorist> (commit `89c6d79`, 2026-09-29), minus `.git`. dmoews's own files (`README.md`, `7094/`, `interpreter/`, the `.iplv` deck, the input formulae and the transcribed 1963 output) are unchanged. Added here:

| File | Role |
|---|---|
| `run.sh` | Builds `lt-stefferud-run.iplv` (deck + input formulae), runs it, prints the comparison table |
| `run-lt.lisp` | Loads `../iplv.lisp` and runs the combined deck |
| `compare.py` | Per-theorem comparison of result, subproblems, substitutions and effort with the 1963 output |
| `lt-stefferud-lisp.out` | Output of the last run |

The deck runs **unmodified**, including the 1963 "save for restart / reload from tape 2" headers and the input-reading code (M89, J180-J186). This differs from the 7094 route in `7094/`, which needed patches.

## Result (2026-10-03)

All 24 theorems get the same result as Stefferud's 1963 run. 23 of them have identical subproblem and substitution counts, and their printed search traces and proofs match line for line. The rest of the output differs only as follows:

- **Effort** is about 0.66 × the 1963 figure for every theorem, because our interpreter counts cycles differently. dmoews's Python interpreter has the same kind of difference.
- ***2.15*** fails in both runs because it hits the 200000 effort limit. Our effort grows more slowly, so we get further first: 48 subproblems vs 31. The first 31 match the 1963 list.
- **Rejected-problem lines** start with an internal symbol, which is a core address in 1963 (`5088`). We print our internal cell number (`118882`). It is two columns wider, so `REJECTED PROBLEM` is cut at column 80. 1963 truncates its own long lines the same way.
- **Transcription noise in the 1963 file:** `DFF.` for `DEF.` (*1.01 in the *2.14 proof), two missing commas in *3.13/*3.14 subproblem lines, and blank-line spacing.

## Interpreter fixes this required (all in `../iplv.lisp`, marked `[Fixed: …]`/`[Added: …]`)

See `../CHANGES_FROM_UPSTREAM.md`, section "Stefferud LT (dmoews deck)".

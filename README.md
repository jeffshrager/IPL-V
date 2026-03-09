# IPL-V Interpreter & Logic Theorist Simulation

A faithful simulation of the **Logic Theorist** (LT) — one of the first automated
theorem-proving programs in the history of artificial intelligence — running on a
re-implemented **IPL-V** (Information Processing Language V) interpreter written in
Common Lisp.

## Historical Background

The Logic Theorist was created by Allen Newell, J.C. Shaw, and Herbert Simon at the
RAND Corporation and Carnegie Mellon University around 1955–1956. It was arguably the
first program to perform a task that, if done by a human, would be called "thinking":
it discovered proofs of theorems in propositional logic by heuristic search through a
space of possible proof steps.

LT was implemented in **IPL-V**, a list-processing language designed by the same team.
IPL-V is, in a meaningful sense, a direct ancestor of Lisp. It runs on an abstract
register machine with a push-down stack (H0), working registers (W0–W31), and a
symbol table of cells. Programs are written as sequences of "cards" (instructions),
each naming a primitive operation (J-function), with conditional branching on a status
flag (H5).

This project re-implements the IPL-V interpreter in SBCL Common Lisp and runs the
original LT program code (transcribed from the 1963 Stefferud technical report) against
a suite of theorems from *Principia Mathematica*.

## What It Proves

The LT attempts to prove theorems in propositional logic using the axioms of
*Principia Mathematica* (Chapter 2). The notation used in `LTFixed.liplv`:

| Symbol | Meaning |
|--------|---------|
| `I`    | Implication (→) |
| `V`    | Disjunction (∨) |
| `*`    | Conjunction (∧) |
| `-`    | Negation (¬) |
| `=`    | Biconditional (↔) |
| `.=.`  | Definitional equality |

**Axioms** (given, not proved):
- `*1.2  (AVA)IA`
- `*1.3  BI(AVB)`
- `*1.4  (AVB)I(BVA)`
- `*1.5  (AV(BVC))I(BV(AVC))`
- `*1.6  (BIC)I((AVB)I(AVC))`

**Theorems attempted** (a subset of *Principia Mathematica* Chapter 2):

| Theorem | Formula | Result |
|---------|---------|--------|
| 2.01 | `(PI-P)I-P` | PROOF FOUND |
| 2.02 | `QI(PIQ)` | PROOF FOUND |
| 2.04 | `(PI(QIR))I(QI(PIR))` | PROOF FOUND |
| 2.05 | `(QIR)I((PIQ)I(PIR))` | PROOF FOUND |
| 2.06 | `(PIQ)I((QIR)I(PIR))` | PROOF FOUND |
| 2.07 | `PI(PVP)` | PROOF FOUND |
| 2.08 | `PIP` | PROOF FOUND |
| 2.10 | `-PVP` | PROOF FOUND |
| 2.11 | `PV-P` | PROOF FOUND |
| 2.12 | `PI--P` | PROOF FOUND |
| 2.13 | `PV---P` | PROOF FOUND |
| 2.14 | `--PIP` | NO PROOF FOUND |
| 2.15 | `(-PIQ)I(-QIP)` | NO PROOF FOUND |
| 2.20 | `PI(PVQ)` | PROOF FOUND |
| 2.21 | `-PI(PIQ)` | NO PROOF FOUND |
| 2.24 | `PI(-PVQ)` | PROOF FOUND |
| 3.13 | `(-(P*Q))I(-PV-Q)` | NO PROOF FOUND |
| 3.14 | `(-PV-Q)I(-(P*Q))` | NO PROOF FOUND |
| 3.24 | `-(P*-P)` | NO PROOF FOUND |
| 4.13 | `P=--P` | NO PROOF FOUND |
| 4.20 | `P=P` | PROOF FOUND |
| 4.24 | `P=(P*P)` | PROOF FOUND |
| 4.25 | `P=(PVP)` | PROOF FOUND |

The NO PROOF FOUND results are historically consistent — the original LT also failed
on several of these within its search effort limits.

## Requirements

- [SBCL](http://www.sbcl.org/) (Steel Bank Common Lisp), tested with version 2.2.6
- [Quicklisp](https://www.quicklisp.org/) with `fiveam` (used for testing utilities)

## Running

From the `LT/` directory start SBCL and evaluate at the repl:

    (load (compile-file "iplv.lisp"))

Output is written to the repl. A complete run takes approximately
574,000 IPL machine cycles (and finishes in under a minute on modern
hardware), who knows how long that might have been on the JOHNNIAC at
RAND in 1956!

> **Note:** Do not change the compiler settings in `iplv.lisp` from
> `(debug 3) (safety 3) (speed 0)`. These are required for correct behavior.

## Reading the Output

Each output line is prefixed with `::::::::::::::::::::::::::::::::`. Key things to
look for:

```
2.01    (PI-P)I-P                       ← theorem being attempted

PROOF FOUND.                            ← success

    GIVEN           2.0   (AVA)IA       ← proof derivation
    SUBSTITUTION    .0    (PI-P)IP
    SUBLEVEL REPL   2.01  (PI-P)I-P
    Q.E.D.

EFFORT         LIMIT 20000   ACTUAL 5579     ← search statistics
SUBPROBLEMS    LIMIT 50      ACTUAL 1
SUBSTITUTIONS  LIMIT 50      ACTUAL 2
```

**Proof methods** used by the LT:
- **SUBSTITUTION** — substitute variables in an axiom or proved theorem
- **DETACHMENT** (modus ponens) — from `AIB` and `A`, conclude `B`
- **FORWARD CHAINING** — apply substitution + detachment forward
- **BACKWARD CHAINING** — work backwards from the goal
- **SUBLEVEL REPLACEMENT** — replace a subexpression using a definition

**Effort** counts IPL machine cycles (individual instruction executions) from the
start of a proof attempt. The 20,000-cycle limit is a soft cap: it stops the search
from *beginning* another subproblem exploration once exceeded, but cannot interrupt
an in-progress search. Some successful proofs can exceed 20,000 total cycles.

## Architecture

### IPL-V Machine

The interpreter (`iplv.lisp`) implements the IPL-V abstract machine:

- **Cell**: the fundamental data unit, with fields `p`, `q`, `symb`, `link`
- **`*symtab*`**: hash table mapping symbol names to cells (the "memory")
- **H0**: main push-down stack — all J-function I/O flows through it
- **H3**: cycle counter
- **H5**: status flag (`"+"` success / `"-"` failure) — controls branching
- **W0–W31**: working registers with their own push-down stacks
- **J-functions**: ~60 primitive operations (`defj` macro), from `J0` (no-op) to
  `J186` (read input)

### Execution

`ipl-eval` runs one card at a time. Each card specifies:
- **q field**: how to fetch the operand (q=0: use symb directly; q=1: indirect; q=2: double-indirect)
- **p field**: what to do with it (p=0: execute; p=1: push to H0; p=2: output from H0; p=7: branch if H5–)
- **symb**: the operation or operand
- **link**: the next card (blank = sequential; non-blank = explicit jump)

### Loader

`load-ipl` reads `.liplv` files (S-expression format). Data sections (following a
`type=5, q=1` marker) store integer values in `cell-link` (as Lisp integers) and
alpha strings in `cell-symb`. Code sections link cards sequentially and resolve local
symbols.

## Reference Documents

- **Stefferud (1963)** — *The Logic Theory Machine: A Model Heuristic Program*,
  RAND RM-3731. The primary reference for LT's M-routine semantics.
- **Newell (1964)** — *Information Processing Language V Manual*, 2nd ed. The
  definitive reference for IPL-V J-function semantics, cell structure, and generator
  protocol.
- **Simon's J-functions** (`simonsjs.txt`) — Simon's original assembly-level IPL-V
  implementations of the J-functions; cross-checked when bugs arise. (Thanks to the
  Computer History Museum: [Simon's J's (Computer History Museum)](https://computerhistory.org/blog/simons-js/).

## License

The IPL-V interpreter code (`iplv.lisp`) and LT transcription (`LTFixed.liplv`) are
original research/reconstruction work. The historical documents in `IPL-V/` and `LT/`
are reproduced for academic research purposes.

```
;;; ===================================================================
;;; Copyright 2025-2026 by Jeff Shrager
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining
;;; a copy of this software and associated documentation files (the
;;; “Software”), to deal in the Software without restriction, including
;;; without limitation the rights to use, copy, modify, merge, publish,
;;; distribute, sublicense, and/or sell copies of the Software, and to
;;; permit persons to whom the Software is furnished to do so, subject to
;;; the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;;  included in all copies or substantial portions of the Software.
;;;;
;;; THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
;;; BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
;;; ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
;;; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;;; SOFTWARE.
;;; ===================================================================
```

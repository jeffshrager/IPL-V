# An IPL-V interpreter in Common Lisp that runs the original Logic Theorist 

The goal of this project is a faithful reanimation of the earliest AIs
-- actally cogntiive models -- created by the team of Newell, Simon,
and Shaw (NSS) at RAND and Carnegie Tech (now CMU) in the 1950s. These
programs were created in a programming language called
[IPL](https://en.wikipedia.org/wiki/Information_Processing_Language),
which NSS created specifically for building cognitive models.

The first of these models, and the first one I have got working, is
the [**Logic Theorist**](https://en.wikipedia.org/wiki/Logic_Theorist)
(LT). LT was a heuristic theorem-prover for propositional logic. As
such, LT was also the first AI.

Fortunately, LT was extremely well documented in a 1963 paper by
Stefferud (see refs), as was the fifth version of IPL, IPL-V, in 1964
manual by Newell et al. Here I have created my own IPL-V emulator, in
Common Lisp, that correctly runs LT from the Stefferud paper with no
significant changes.

## Historical Background

The Logic Theorist was created by [Allen
Newell](https://en.wikipedia.org/wiki/Allen_Newell), [J.C. (Cliff)
Shaw](https://en.wikipedia.org/wiki/Cliff_Shaw), and [Herbert
Simon](https://en.wikipedia.org/wiki/Herbert_A._Simon) at the RAND
Corporation and Carnegie Tech (now CMU) around 1955–1956. It was
arguably the first AI -- a program to perform a task that, if done by
a human, would be called "thinking": it discovered proofs of theorems
in propositional logic by heuristic search through a space of possible
proof steps.

(Arguably Art Samuel's checkers player existed a couple years before
LT. It was also heuristic, but Samuel's goal was to build a checkers
player, vs. NSS whose explicit goal was to model human cognition, and
did so in many domains. NSS had explicit hypotheses about how human's
reasoned, and about the "physical symbol system" that underlies (by
hypothesis) intellignce. I don't mean to be dissing Samuel's brilliant
effort. He also built the first machine learning program, and the
first GAN!)

LT was implemented in **IPL**, a list-processing language designed
by the same team, and implemented initially on the
[JOHNNIAC](https://en.wikipedia.org/wiki/JOHNNIAC), one of the first
Turing-Von Neumann, so-called IAS or "Princeton" machines, built at
RAND (and named after Von Neumann). The JOHNNIAC had 4,096 40-bit words.

IPL is, in a meaningful sense, a direct ancestor of Lisp. It runs on
an abstract register machine with push-down stacks, working
registers, and a symbol table of cells. Directly foreshadowing Lisp,
symbol and list processing are the dominant paradigm in IPL-V:
Everything, including routines, is a list of symbols (or,
occasionally, numerical data). Again, like lisp, language primitives
that are not basic machine functions (like pushing or popping a stack)
are called "J-Functions" and are themselves written in IPL.

IPL-V (IPL-five) was the only version of IPL publicly released. I
implemented a complete IPL-V interpreter in Common Lisp based on the
1964 IPL-V manual by Newell, et al. It runs the original LT program
code, transcribed directly from the 1963 Stefferud technical report
(see refs). I had to make a very small number of changes, mostly
having to do with the fact that the original depended on some odd
details of the BCD character set. More than 99% of the LT code running
here is the original code from the Stefferud paper.

## What LT Proves

The LT attempts to prove theorems in propositional logic using the
axioms of *Principia Mathematica* (Chapter 2). The notation used by
the original authors is:

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

```
    (load (compile-file "iplv.lisp"))
```

Output is written to the repl. A complete run with the default inputs
(as above) takes approximately 574,000 IPL machine cycles (and
finishes in just a few seconds on modern hardware -- a little slower
for output). Who knows how long that might have taken on the JOHNNIAC
at RAND in 1956; probably hours.

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

The Stefferud paper describes all this in detail.

## The LT Code

[LT was transcribed into a google
sheet](https://docs.google.com/spreadsheets/d/1ibvbyoIT20R4gDqo2iSkk5mJBWsRrtQ6sr8Fj1nz910/edit?gid=0#gid=0)
from Stefferud's 1963 paper by me and Anthony Hay. A bit
later several typos were discovered by Rupert Lane, using [his
"gridlock" process and software that can correctly extract code from
PDFs](https://github.com/rupertl/gridlock).

Note that the file called "LTFixed.liplv" is "Fixed" in the sense that
it's not quite a pure dump of the code in the Stefferud paper. I had
to make a small number of minor changes, mostly having to do with the
fact that the JOHNNIAC was a BCD machine, so characters are handled
... weirdly. Also, to make usage a little simpler I moved some of the
parameters to the end where they can be easily edited. Conveniently,
Lisp comment chars (;) work in .liplv files, so these changes have
been documnted in the "Fixed" file. Overall, I think it's safe to say
that more than 99% of the code is just as in the original paper.

## The Emulated IPL-V Machine

The original IPL-V was also emulated, originally on the JOHNNIAC at
RAND, and then on a wide range of machines through the mid 1960s,
before it was overtaken by Lisp.

My interpreter (`iplv.lisp`) implements the IPL-V abstract machine as
described in Newell et al's 1964 manual (see refs, below). (load-ipl
...) reads `.liplv` files, which are S-expression formatted IPL-V.

After loading (ipl-eval ...) is passed a single symbol at which to
begin execution, as specified in the "TYPE=5" card just before the
axioms and theorems to be proved:

  ```
  ("KICK OFF FOR PROVING THEOREMS" "5" "" "" "" "X1" "" "" "")
  ```

This will start at the symbol (routine called) "X1")

## Inputs

Immediately after the "TYPE=5" card (above) are the inputs to the
program. There are two sections, separated by a blank line. The
expressions before the blank are the axioms that proofs will depend
upon, and the ones after the blank are the statements to be proved.

**An important part of the LT is that it treats proven expressions as
axioms, so that it can prove more and more complex expressions! In
this sense, it learns -- maybe it's the world's first machine learning
program?**

## Other IPL-V code

If you look at the end of iplv.lisp, where execution starts, you'll
see that there are several other IPL-V programs that I've used
variously for testing. Probably of greatest interest is Newell's
implementation of the Ackermann function. There are also some of the
examples from Newell et al's 1964 IPL-V manual.

## Acknowledgements

The following folks (in random order) helped in a bunch of different
ways: Ant Hay, Gemini, Rupert Lane, Amy Majczyk, Leigh Klotz, Art
Schwarz, David M. Berry, Claude, Ethan Ableman, Paul McJones. If I've
forgotten you my apologies and please remind me!

I want to also thank Al Newell and Herb Simon, who I studied under at
CMU in the 1980s. IPL and LT were long since history by that time, and
I never spoke with them about either of these; We barely even learned
about these brilliant pioneering efforts in our classes. But something
from my working with these giants stuck with me. At CMU I was working
on modeling scientific and engineering reasoning, and continued to do
so for more-or-less the rest of my career. Now, at the end of that
career, I've been led back to try to understand how these brilliant
scientist-engineers were inventing AI and cognitive science.

## References

- **Stefferud (1963)** — *The Logic Theory Machine: A Model Heuristic Program*,
  RAND RM-3731. The primary reference for LT's M-routine semantics.
- **Newell, et al. (1964)** — *Information Processing Language V Manual*, 2nd ed. The
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

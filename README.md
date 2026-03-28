# An IPL-V interpreter in Common Lisp that runs the original Logic Theorist

See this paper for a more correct and detailed history:

     https://arxiv.org/abs/2603.13514

The goal of this project is a faithful reanimation of the earliest AIs
— actually cognitive models — created by the team of Newell, Simon,
and Shaw (NSS) at RAND and Carnegie Tech (now CMU) in the 1950s. These
programs were created in a programming language called
[IPL](https://en.wikipedia.org/wiki/Information_Processing_Language),
which NSS created specifically for building cognitive models.

The first of these models, and the first one I have got working, is
the [**Logic Theorist**](https://en.wikipedia.org/wiki/Logic_Theorist)
(LT). LT was a heuristic theorem-prover for propositional logic. As
such, LT was also the first AI.

Fortunately, LT was extremely well documented in a 1963 paper by
Stefferud (see refs), as was the fifth version of IPL, IPL-V, in the
1964 manual by Newell et al. Here I have created my own IPL-V
interpreter, in Common Lisp, that correctly runs LT from the
Stefferud paper with no significant changes.

## Historical Background

The Logic Theorist was created by [Allen
Newell](https://en.wikipedia.org/wiki/Allen_Newell), [J.C. (Cliff)
Shaw](https://en.wikipedia.org/wiki/Cliff_Shaw), and [Herbert
Simon](https://en.wikipedia.org/wiki/Herbert_A._Simon) at the RAND
Corporation and Carnegie Tech (now CMU) around 1955–1956. It was
arguably the first AI — a program to perform a task that, if done by
a human, would be called "thinking": it discovered proofs of theorems
in propositional logic by heuristic search through a space of possible
proof steps.

(Arguably Art Samuel's checkers player existed a couple years before
LT. It was also heuristic, but Samuel's goal was to build a checkers
player, vs. NSS whose explicit goal was to model human cognition, and
did so in many domains. NSS had explicit hypotheses about how humans
reasoned, and about the "physical symbol system" that underlies (by
hypothesis) intelligence. I don't mean to be dissing Samuel's
brilliant effort. He also built the first machine learning program,
and the first GAN!)

LT was implemented in **IPL**, a list-processing language designed
by the same team, and implemented initially on the
[JOHNNIAC](https://en.wikipedia.org/wiki/JOHNNIAC), one of the first
Turing–Von Neumann, so-called IAS or "Princeton" machines, built at
RAND (and named after Von Neumann). The JOHNNIAC had 4,096 40-bit words.

IPL is, in a meaningful sense, a direct ancestor of Lisp. It runs on
an abstract register machine with push-down stacks, working
registers, and a symbol table of cells. Directly foreshadowing Lisp,
symbol and list processing are the dominant paradigm in IPL-V:
everything, including routines, is a list of symbols (or,
occasionally, numerical data). Again, like Lisp, language primitives
that are not basic machine functions (like pushing or popping a
stack) are called "J-Functions" and are themselves written in IPL.

IPL-V (IPL-five) was the only version of IPL publicly released. I
implemented a complete IPL-V interpreter in Common Lisp based on the
1964 IPL-V manual by Newell, et al. It runs the original LT program
code, transcribed directly from the 1963 Stefferud technical report
(see refs). I had to make a very small number of changes, mostly
having to do with the fact that the original depended on some odd
details of the BCD character set. More than 99% of the LT code
running here is the original code from the Stefferud paper.

## Key Files

| File | Purpose |
|------|---------|
| `iplv.lisp` | Generic IPL-V interpreter (~2950 lines). No LT-specific code. |
| `lt.lisp` | Loads `iplv.lisp`, adds LT proof-graph analysis, runs `LTFixed.liplv`. |
| `LTFixed.liplv` | LT program and theorems in IPL-V S-expression format. |
| `ltresults/` | Created automatically; holds timestamped logs and dotstar files. |

## Requirements

- [SBCL](http://www.sbcl.org/) (Steel Bank Common Lisp), tested with version 2.2.6
- [Graphviz](https://graphviz.org/) `dot` command (optional, for rendering proof graphs)

## Running

From the repo directory, run:

```
   bash
   sbcl --eval '(load (compile-file "lt.lisp"))' 
```

`lt.lisp` loads the IPL-V interpreter, then runs the Logic Theorist
against all theorems in `LTFixed.liplv`. A complete run takes
approximately 574,000 IPL machine cycles and finishes in a few seconds
on modern hardware.

> **Note:** Do not change the compiler settings in `iplv.lisp` from
> `(debug 3) (safety 3) (speed 0)`. These are required for correct behavior.

### Output Files

Each run automatically creates two timestamped files in `ltresults/`:

```
ltresults/
  202603181403.log       ← complete LT output (everything printed to stdout)
  202603181403.dotstar   ← all proof graphs concatenated (one per theorem)
```

Individual per-theorem `.dot` files are also written to `/tmp/lt-proof-NNN.dot`
(e.g. `/tmp/lt-proof-425.dot` for theorem *4.25).

### Rendering Proof Graphs

Short story:

     prf2pdf.sh <dotstar> <theorem> [output]

Long story:

To render an individual proof graph as a PDF:

```bash
dot -Tpdf /tmp/lt-proof-425.dot -o proof-425.pdf
```

To render a graph from a dotstar file, extract each `digraph { }` block
and run `dot` on it, or use a script that splits on the `// ====` separators.

The dotstar format is straightforward: each theorem's graph is preceded by:

```
// ============================================================
// Problem *4.25
// ============================================================
digraph "Problem *4.25" {
  ...
}
```

### Proof Graph Colors

| Color | Meaning |
|-------|---------|
| Blue ellipse | Root (the theorem being attempted) |
| Green | Method succeeded (H5+) |
| Pink | Method failed (H5−) |
| Gold | M19 Derivation: sub-problem accepted/queued |
| Gray | M19 Derivation: sub-problem rejected |

## Reading the LT Output

Each output line is prefixed with `::::::::::::::::::::::::::::::::`. Key things to look for:

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

**Proof methods** used by LT:
- **SUBSTITUTION** — substitute variables in an axiom or proved theorem
- **DETACHMENT** (modus ponens) — from `AIB` and `A`, conclude `B`
- **FORWARD CHAINING** — apply substitution + detachment forward
- **BACKWARD CHAINING** — work backwards from the goal
- **SUBLEVEL REPLACEMENT** — replace a subexpression using a definition

**Effort** counts IPL machine cycles from the start of a proof attempt.
The 20,000-cycle limit is a soft cap: it stops the search from *beginning*
another subproblem exploration once exceeded, but cannot interrupt an
in-progress search.

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

**Definitions** (used in substitution):
- `*1.01  (PIQ) .=. (-PVQ)`
- `*2.33  (PVQVR) .=. ((PVQ)VR)`
- `*3.01  (P*Q) .=. -(-(PV-Q))`
- `*4.01  (P=Q) .=. ((PIQ)*(QIP))`

**Theorems attempted** (a subset of *Principia Mathematica* Chapters 2–4):

| Theorem | Formula | Result |
|---------|---------|--------|
| *2.01 | `(PI-P)I-P` | PROOF FOUND |
| *2.02 | `QI(PIQ)` | PROOF FOUND |
| *2.04 | `(PI(QIR))I(QI(PIR))` | PROOF FOUND |
| *2.05 | `(QIR)I((PIQ)I(PIR))` | PROOF FOUND |
| *2.06 | `(PIQ)I((QIR)I(PIR))` | PROOF FOUND |
| *2.07 | `PI(PVP)` | PROOF FOUND |
| *2.08 | `PIP` | PROOF FOUND |
| *2.10 | `-PVP` | PROOF FOUND |
| *2.11 | `PV-P` | PROOF FOUND |
| *2.12 | `PI--P` | PROOF FOUND |
| *2.13 | `PV---P` | PROOF FOUND |
| *2.14 | `--PIP` | NO PROOF FOUND |
| *2.15 | `(-PIQ)I(-QIP)` | NO PROOF FOUND |
| *2.20 | `PI(PVQ)` | PROOF FOUND |
| *2.21 | `-PI(PIQ)` | PROOF FOUND |
| *2.24 | `PI(-PVQ)` | NO PROOF FOUND |
| *3.13 | `(-(P*Q))I(-PV-Q)` | NO PROOF FOUND |
| *3.14 | `(-PV-Q)I(-(P*Q))` | NO PROOF FOUND |
| *3.24 | `-(P*-P)` | NO PROOF FOUND |
| *4.13 | `P=--P` | PROOF FOUND |
| *4.20 | `P=P` | PROOF FOUND |
| *4.24 | `P=(P*P)` | NO PROOF FOUND |
| *4.25 | `P=(PVP)` | PROOF FOUND |

The NO PROOF FOUND results are historically consistent — the original
LT also failed on several of these within its search effort limits.

## The Two-File Architecture

The code is split so that the IPL-V interpreter is completely generic:

- **`iplv.lisp`** — the interpreter, J-function library, loader, and
  debug utilities. It defines `defgeneric` hooks (`ipl-eval`,
  `ipl-descend`, `ipl-ascend`) that analysis layers can attach to via
  CLOS `:before`/`:after` methods. It contains a few quoted-out demo
  programs (R3, Ackermann, EPAM) at the end.

- **`lt.lisp`** — loads `iplv.lisp`, then adds:
  - Proof-graph infrastructure (`*proof-graph-methods*`, `proof-graph!`, etc.)
  - M19 annotation capture (records which axiom/method each derivation used)
  - CLOS `:before` methods on `ipl-descend`/`ipl-ascend` to record the call tree
  - `*trace-exprs*` hooks at M001R000/R220/R260 to bracket each theorem's proof
  - The timestamped log/dotstar output to `ltresults/`
  - The `load-ipl` call that actually runs `LTFixed.liplv`

## The LT Code

[LT was transcribed into a Google
Sheet](https://docs.google.com/spreadsheets/d/1ibvbyoIT20R4gDqo2iSkk5mJBWsRrtQ6sr8Fj1nz910/edit?gid=0#gid=0)
from Stefferud's 1963 paper by me and Anthony Hay. A bit later several
typos were discovered by Rupert Lane, using [his "gridlock" process
and software that can correctly extract code from
PDFs](https://github.com/rupertl/gridlock).

Note that the file called `LTFixed.liplv` is "Fixed" in the sense that
it's not quite a pure dump of the code in the Stefferud paper. I had to
make a small number of minor changes, mostly having to do with the fact
that the JOHNNIAC was a BCD machine, so characters are handled oddly.
Also, to make usage a little simpler I moved some of the parameters to
the end where they can be easily edited. Conveniently, Lisp comment
chars (`;`) work in `.liplv` files, so these changes have been
documented in the "Fixed" file. Overall, more than 99% of the code is
just as in the original paper.

## Other IPL-V Programs

At the end of `iplv.lisp` (commented out with a leading quote `'(progn
...)`) are several other IPL-V programs used variously for testing:
Newell's implementation of the Ackermann function, call-stack state
machine tests (T123), some examples from the 1964 IPL-V manual, and
EPAM. To run one, remove the leading `'` and run `iplv.lisp` directly
(not `lt.lisp`).

## Acknowledgements

The following folks (in random order) helped in a bunch of different
ways: Ant Hay, Gemini, Rupert Lane, Amy Majczyk, Leigh Klotz, Art
Schwarz, David M. Berry, Claude, Ethan Ableman, Paul McJones. If I've
forgotten you my apologies and please remind me!

I also want to thank Al Newell and Herb Simon, who I studied under at
CMU in the 1980s. IPL and LT were long since history by that time, and
I never spoke with them about either of these; we barely even learned
about these brilliant pioneering efforts in our classes. But something
from my working with these giants stuck with me. At CMU I was working
on modeling scientific and engineering reasoning, and continued to do
so for more-or-less the rest of my career. Now, at the end of that
career, I've been led back to try to understand how these brilliant
scientist-engineers were inventing AI and cognitive science.

## References

- **Stefferud (1963)** — *The Logic Theory Machine: A Model Heuristic Program*,
  RAND RM-3731. The primary reference for LT's M-routine semantics.
- **Newell, et al. (1964)** — *Information Processing Language V Manual*, 2nd ed.
  The definitive reference for IPL-V J-function semantics, cell structure,
  and generator protocol.
- **Simon's J-functions** (`simonsjs.txt`) — Simon's original assembly-level
  IPL-V implementations of the J-functions; cross-checked when bugs arise.
  (Thanks to the Computer History Museum:
  [Simon's J's](https://computerhistory.org/blog/simons-js/).)

## License

The IPL-V interpreter code (`iplv.lisp`), LT runner (`lt.lisp`), and LT
transcription (`LTFixed.liplv`) are original research/reconstruction work.
The historical documents in `IPL-V/` and `LT/` are reproduced for academic
research purposes.

```
;;; ===================================================================
;;; Copyright 2025-2026 by Jeff Shrager
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining
;;; a copy of this software and associated documentation files (the
;;; "Software"), to deal in the Software without restriction, including
;;; without limitation the rights to use, copy, modify, merge, publish,
;;; distribute, sublicense, and/or sell copies of the Software, and to
;;; permit persons to whom the Software is furnished to do so, subject to
;;; the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;;  included in all copies or substantial portions of the Software.
;;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
;;; BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
;;; ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
;;; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;;; SOFTWARE.
;;; ===================================================================
```

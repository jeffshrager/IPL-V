# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is an **IPL-V (Information Processing Language V) interpreter** written in Common Lisp, used to simulate the historic **Logic Theorist** — one of the first automated theorem-proving programs (Newell, Shaw, Simon, 1950s-60s).

### Reference Documents (in `../IPL-V/` and `../LT/`)

- **`../LT/1963_Stefferud_LT_RM-3731_OCRed.pdf`** — The Logic Theorist program specification. When debugging LT behavior, consult this for the correct semantics of M-routines (M1, M42, M54, etc.) and proof search strategy.
- **`../IPL-V/1964-Newell-Information_Processing_Language-V_Second_Edition_1964_OCRED.pdf`** — The IPL-V language manual (2nd ed., 1964). This is the authoritative reference for J function semantics, cell/list structure, generator protocol, and H/W register conventions. Page numbers referenced in code comments (e.g., `[186]`, `p. 179`, `p. 181`) refer to this manual.
- **`../IPL-V/IPL-V_CheatSheet.pdf`** — Quick reference for IPL-V primitives.
- **`../IPL-V/simonsjs.txt`** — Simon's original J function implementations in assembly-like IPL-V notation (useful for cross-checking `defj` implementations).

## Running the Interpreter

```bash
rm iplv.out; sbcl --lose-on-corruption --eval '(progn (load (compile-file "iplv.lisp")) (backtrace))' >> iplv.out
```

This compiles and runs `iplv.lisp`, which automatically loads and executes `LTFixed.liplv` (the Logic Theorist program). Output goes to `iplv.out`.

**Do not lower the safety/debug compiler settings** — the code comment warns these must stay at `(debug 3) (safety 3) (speed 0)` or things break for unknown reasons.

## Key Files

- `iplv.lisp` — The complete IPL-V interpreter (~2930 lines)
- `LTFixed.liplv` — Logic Theorist code and test theorems in IPL-V syntax
- `../GEMINI.md` — Debugging guide (read this carefully before debugging)
- `../notes.txt` — History of past bugs and fixes

## Configuring Tests and Traces

At the end of `iplv.lisp`, the `progn` block controls what runs. Multiple commented-out test blocks exist for R3, F1, Ackermann, T123, and EPAM scenarios.

The LT theorem syntax in `LTFixed.liplv`: `I` = implication, `V` = OR, `*` = AND, `-` = NOT. Axioms appear before the blank line; theorems to prove appear after.

### Debugging Traces

Add trace hooks inside `*breaks*` entries using cycle number, card ID (e.g., `"M088R020"`, partial keys work), or arbitrary Lisp expressions:

```lisp
;; Start tracing at cycle 2600
(2600
  (setf *!!* '(:run :jcalls) *cell-tracing-on* t)
  (setf *trace-cell-names-or-exprs* '("H0" "W0" "W1" "W2") *cell-tracing-on* t))

;; Break at cycle 2650
(2650 (break))

;; Print cycle counter every 100 cycles (useful for finding break locations)
((zerop (mod (h3-cycles) 100)) (print (h3-cycles)))
```

**Avoid full traces from cycle 0** — the output is enormous. Start with `:jcalls` only, then narrow down.

Trace mode flags: `:run`, `:jcalls`, `:jdeep`, `:dr-memory`, `:load`, `:gentrace`, `:alerts`

Useful debug utilities:
- `(pl "symbol")` — print a list bound to a symbol (works with local `"9-1234"` style names too)
- `(pll "symbol")` — print a linear list
- `(trace!)` — show current trace state

## Architecture

### Data Model

The fundamental unit is a **cell** (struct with fields): `type`, `name`, `sign`, `p`, `q`, `symb`, `link`, `id`, `comments`. All cells live in `*symtab*` (a hash table keyed by string name).

**Special registers:**
- `H0` — Main processing stack (LIFO, central to all J function operation)
- `H3` — Cycle counter
- `H5` — Status flag: `"+"` (success) or `"-"` (failure); controls conditional branching and generator termination
- `W0`–`W31` — Working registers
- `*genstack*` — Private stack for generator operations

### J Functions (Primitives)

Defined via `(defj ...)` macro. These are the IPL-V primitive operations (J0–J100+). **Almost all bugs are in J function implementations, not in the LT application code** (`LTFixed.liplv`).

Critical behavioral rules for J functions:
1. Pop inputs from H0 before processing; push outputs onto H0 after
2. Always explicitly set H5+ on success — do not rely on inherited status (past bugs: J64 failed to set H5+ on success, causing H5- to propagate into generators)
3. J100 (generator): terminate if subprocess returns H5-
4. Generator operations (J17–J19) use `*genstack*`; do not manipulate it directly

**J Function Quick Reference** (consult IPL-V manual for full semantics):

| J# | Description |
|----|-------------|
| J0 | No operation |
| J1 | Execute process (0) |
| J2 | Test (0) == (1) |
| J3/J4/J5 | Set H5- / Set H5+ / Reverse H5 |
| J6 | Reverse (0) and (1) |
| J7 | Halt |
| J8 | Restore H0 (pop) |
| J9 | Erase cell (0) |
| J10 | Find value of attribute (0) of (1) on DL |
| J11 | Assign (1) as value of attribute (0) of (2) |
| J14 | Erase attribute (0) of (1) |
| J15 | Erase all attributes of (0) |
| J17 | Generator setup |
| J18 | Execute subprocess (generator step) |
| J19 | Generator cleanup |
| J20–J29 | Move (0)-(n) into W0–Wn |
| J30–J39 | Restore Wn |
| J40–J49 | Preserve Wn |
| J50–J53 | Preserve Wn then move (0)-(n) into W0–Wn |
| J60 | Locate next symbol after cell (0) |
| J62 | Locate (0) on list (1) |
| J63 | Insert (0) before symbol in (1) |
| J64 | Insert (0) after symbol in (1) |
| J65 | Insert (0) at end of list (1) |
| J66 | Insert (0) at end of list (1) if not already on it |
| J68 | Delete symbol in cell (0) |
| J71 | Erase list (0) |
| J72 | Erase list structure (0) |
| J73 | Shallow copy list (0) [manual p.186] |
| J74 | Deep copy list structure (0) [manual p.186] |
| J75 | Divide list after location (0) |
| J76 | Insert list (0) after cell (1) and locate last symbol |
| J78 | Test if list (0) is not empty |
| J79 | Test if cell (0) is not empty |
| J80 | Find head symbol of (0) |
| J81/J82 | Find 1st/2nd non-head symbol of (0) |
| J90 | Create blank cell on H0 |
| J91–J93 | Create list of 1/2/3 entries |
| J100 | Generate symbols from list (1) for subprocess (0) |
| J110/J111 | Add/subtract (1) and (2) into (0) |
| J114–J117 | Numeric comparisons |
| J120 | Copy (0) |
| J121 | Set (0) identical to (1) |
| J124 | Clear (0) |
| J125 | Tally 1 in (0) |
| J126 | Count list (0) |
| J130/J132 | Test if (0) is regional/local symbol |
| J133 | Test if list (0) has been marked processed |
| J136 | Make symbol (0) local |
| J137 | Mark list (0) processed |
| J138 | Make symbol (0) internal |
| J151/J152 | Print list/symbol |
| J154/J155 | Clear/print line |
| J156/J157 | Enter symbol/data term left-justified |
| J160/J161 | Tab to col / increment column |
| J180–J186 | Input/read operations |

### Execution Engine

`ipl-eval` / `call-ipl-prim` execute one "card" (instruction) at a time. Cards have: a symbolic name, P/Q fields for control flow, and conditional branching on H5 status (+ branch vs - branch). Execution starts from the `type 5` cell's `symb` field.

### Loader

`load-ipl` reads `.liplv` files (S-expression format). Type 5 cells trigger execution. Supports `:adv-limit` to cap total instruction advances.

## Current Problem (as of Feb 2026)

The Logic Theorist should prove `*2.92 ((PVQ)IQ)` from axioms `*1.21 ((AVB)IA)` and `*1.22 ((AVB)I(BVA))` but currently reports "NO PROOF FOUND". Debugging this is the active work.

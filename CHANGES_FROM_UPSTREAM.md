# Changes to `iplv.lisp` relative to upstream (jeffshrager/IPL-V @ 792cb15)

This is a handoff for merging this interpreter back into the IPL-V repo, where the Logic Theorist (LT), EPAM and the misccode tests live. For the full patch, run `diff <(git -C ~/Desktop/AIHistory/IPL-V/repo show 792cb15:iplv.lisp) lisp/iplv.lisp`. Nearly every change carries a `[Fixed: …]` / `[Added: …]` / `[Changed: …]` comment in the source.

**Tested here:**
- Ackermann: card deck `tests/Acker.Ipl` → 125, and `tests/Ackermann.liplv` → 61.
- J-probe deck `tests/jprobe.card`.
- The Heuristic Coder: `../run.sh`, whose output is `../run/t1*.txt`.
- The annexer: `../annexer/run.sh`.

**NOT tested: LT, EPAM, F1, R3, T123.** Changes marked ⚠ alter behavior that these programs may depend on.

## Loader
1. **Reads 80-column card decks directly.** `load-ipl` looks at the first line: `(:` means `.liplv`, anything else means cards. New functions: `liplv-file?`, `card-cols`, `card-field`, `read-card`, `next-card-row`, `normalize-local`.
   - **Columns:** comment 1-40, type 41, name 43-47, sign 48, PQ 49-50, SYMB 51-55, LINK 57-61, comment 62-70, **id 71-80**.
   - **PQ:** blank means `00`; one blank column counts as 0.
   - **Integer terms (PQ 01):** the value comes from cols 51-61 with blanks removed, signed by col 48.
   - **Alphanumeric terms (PQ 21):** leading blanks are kept, and an all-blank term becomes `" "`.
   - **Skipped cards:** types 1 and 9, and blank cards.
2. **Old-style locals** `9n` → `9-n` (on cards only). ⚠ **A lone `9` is no longer local** (`local-symbol-by-name?`), so it is the internal symbol 9.
3. **Blank SYMB and LINK on the same card** both mean the next card. Previously this was a `break`.
4. **Blanks on a list's last card mean `0`.**
5. **Header Q parity:** even Q → routines, odd Q → data (Q=5 is data). P is ignored. ⚠ Before, only exact `00`/`01` switched mode.
6. **`convert-local-symbols`** skips non-string (numeric) fields.
7. **`create-undefined-regionals`** runs before execution starts. It creates empty `(0,0)` cells for used-but-undefined regional symbols (letter+digits, not H/W/J). ⚠ LT may reference symbols it never defines.
8. The auto-run `simple.liplv` block at the end of the file is quoted out.

## Executor and helpers
9. ⚠ **`numset`**: `(cell-q data-cell) 1` was outside the `setf`, so computed integers were never marked Q=1 (J157 printed them as 0). Now P=0, Q=1 are set.
10. ⚠ **J155** prints the line literally. `hack-output!!` (which dropped a `0` after `(` or `)`) is no longer called; LT may have relied on it. **J156** now enters region-0 symbols compactly (`A0` → `A`), per manual 16.2.
11. ⚠ **J62** now searches from the cell *after* (1) through the last cell. The old helper tested cell (1) itself and never tested the last cell.
12. ⚠ **J68** on the last cell now unlinks it from the previous cell (it emulates a private termination cell; it does a symtab scan). The old code did nothing (H5−).
13. ⚠ **J114** compares alphanumeric terms (P=2, Q=1) as text. Before, it was numeric only.
14. **J60** of a symbol with no cell (the termination symbol `0`) returns H5−. Before, it crashed.
15. ⚠ **J180** clears the line buffer before reading, and reads at most 80 columns.
16. ⚠ **J181** no longer overwrites an existing cell when it inputs a regional symbol.
17. ⚠ **J183/J184 scanner**: (0) gains (found − 1W25), per the manual. Before, (0) was set to the column. This is identical when (0) *is* 1W25, the usual J184 use.

## J-functions added
J12, J13, J61, J69, J70, J77, J83, J101 (emulates head marking), J118, J131, J149 (no-op), J150 (calls `pl`), J165 (no-op). Helpers: `last-cell-of-list`, `value-list-of-attribute`.

## Suggested procedure (for the IPL-V session)
The plan is to **adopt this file wholesale**: copy it over `iplv.lisp` in the IPL-V repo. It is a drop-in replacement. `lt.lisp` only does `(load (compile-file "iplv.lisp"))` and then `(load-ipl "LTFixed.liplv" ...)`, and `.liplv` files still load as before (they are detected by their `(:` header).

1. Save a baseline first, using the old interpreter: `lt.out` and `ltresults/`, plus the Ackermann and EPAM results.
2. Copy this `iplv.lisp` over the old one and rerun LT, EPAM and the misccode tests.
3. If the output differs, use the ⚠ items above as a checklist. The likeliest causes are J62's search start, J68's last-cell deletion, J155 no longer calling `hack-output!!` (LT's `(0`-style symbols), a lone `9` no longer being local, header Q parity, and `create-undefined-regionals`. For each one, decide whether to keep the manual-correct behavior and adjust LTFixed, or to make the change conditional.
4. The auto-run `progn` at the end of the file is quoted out, so loading the file no longer runs `misccode/simple.liplv`. Re-enable it if the IPL-V repo wants that.

## Stefferud LT (dmoews deck), 2026-10-03

This file was copied into the IPL-V repo and then fixed until dmoews's unmodified Stefferud deck (`dmoews/`) reproduced the 1963 output (see `dmoews/README-lisp.md`). The old `LTFixed.liplv` / `lt.lisp` run was **not** rechecked.

Loader:
- A type-5 header with **P=4** (restart mode: "reload from tape") is a no-op, because memory is already in place in a single run. It used to be taken as a start card for symbol `2`.
- **PQ 01 is an integer data term only in data sections.** In routines it means "execute the routine named in SYMB" (LT's `01W5`). The reader used to squeeze cols 51-61 into LINK for every 01 card. `read-card`/`next-card-row` now take the load mode.
- **A lone regional character `A` is read as `A0`**, the same symbol (and what J186 inputs). LT spells it both ways.
- **Non-digits after the region character are dropped**: `YES` → `Y0`. LT's run data has `K31 YES`, which is tested against `Y`.
- An all-blank alphanumeric term is kept as **five** blanks, not one. LT's /16 'DEFINITIONS' has a blank external name, which J157 enters 5 columns wide.

Line I/O (columns are 1-based throughout, per manual §16):
- J180 sets 1W25 = 1 (was 0); J154 sets 1W25 = 1 (was 0).
- J182 reads from column 1W25 (it used to drop the first character), takes the rightmost 5 columns of a longer field, and now sets H5.
- J156/J157 enter at column 1W25.
- J160: 1W25 = 1W21 + (0), with left margin 1, per the manual. It used to be (0).
- J156 prints an internal name `9-nnn` as `nnn`.

J-functions:
- **J68** (non-last cell): the cell it removes is returned to available space (symb/link cleared), and H5+ is set. The stale link used to fool J68's last-cell symtab scan into unlinking the wrong predecessor, which left a stray `0` in LT's theorem lists (M62).
- **J136** no longer overwrites Q of a data term (Q=1 is its type code), so J157 prints J120+J136 copies of integers correctly (LT's subproblem numbers printed as `0.`).

The version of IPL-V interpreted by this code
differs from the version of IPL-V described in [MAN1963]
or [MAN1964] as follows:

* The J-functions implemented are only the following:
`J0` through `J15`, `J17` through `J100`, `J110` through `J128`,
`J130` through `J134`, `J136` through `J138`, `J150` through
`J157`, `J160`, `J161`, `J180` through `J184`, `J186`,
and `J197`. `J16`, `J101` through `J103`, `J129`,
`J158`, `J159`, `J162`, `J185`, and `J189` have not been
implemented, and, also, no monitor system,
in-process loading,
save for restart, or error trap J-functions,
auxiliary storage
processes, read and write processes,
block handling processes, partial word processes,
or miscellaneous processes have been implemented
(except for `J197`.)

* Once the interpreter has been stopped with `J7`,
there is no way to restart it.

* Tracing has not been implemented.  Therefore,
when executed,
Q = 3 and Q = 4 do the same thing as Q = 0.

* Auxiliary storage has not been implemented,
so executing Q = 6 and Q = 7 has not been implemented.

* Executing Q = 5 is used to call low-level routines in the
interpreter, rather than machine-language routines.

* For print processes, setting the printing unit
with `1W20`, the left margin with `1W21`, and the line
spacing with `1W22` has not been implemented.
The interpreter always prints to standard output.

* For line read processes, setting the input unit
with `1W18` has not been implemented.  The interpreter
always reads from standard input.

* `H4` does not exist.

* The predefined W cells available are only
the following: `W0` to `W9`, `W11`, `W24`, `W25`, and `W30`.

* The card types available are only 0 (the same as blank),
1, and 5; others will be ignored.  Also, type 5 should only
be used with NAME blank, P = 0 and Q = 0 or 1, SYMB blank
or regional, and LINK blank.

* Assembly and loading does not necessarily terminate when
a card type 5 with a start symbol is found but will go on
if possible.  The program will eventually start at the last start
symbol read in.

* Regional symbols are not allocated in blocks as directed
by card type 2, but are allocated by a symbol table
as necessary.

* Octal and floating-point data terms have not
been implemented.  (There is some code in the
interpreter to handle floating-point, but overall,
it's not usable.)

* Zero is not signed.

* `J150` through `J152` will print `0` in the `DATA` field
for a data term which is not of string or integer type.

* `J153` will print `0` in the `DATA` field
if called with a symbol which does not name a string or integer data term.

* `J156` will enter the names of local and internal symbols,
if available.  Names of local symbols are prepended by the
preceding regional or internal symbol used as name, followed by a dash.
If the symbol has not been named its internal address will be printed.

* `J157` will enter `0` if called with a symbol which does not
name a string or integer data term.

* The undocumented J functions `J203` through `J212` have been added.
They are mostly not very useful as they are subroutines necessary
to implement the other J functions.

* There are additional H cells `H6` through `H11`, which are used
by the generator implementation.

## References

[MAN1963] _IPL-V Programmers' Reference Manual_,
ed. Allen Newell,
RAND Research Memorandum RM-3739-RC,
June 1963,
<https://www.rand.org/pubs/research_memoranda/RM3739.html>.

[MAN1964] _Information Processing Language-V Manual_, second ed., Allen Newell et al., RAND Corporation,
pub.  Englewood Cliffs, NJ: Prentice-Hall, Inc., 1964,
<https://archive.org/details/bitsavers_randiplInfanguageVSecondEdition1964_15001417>.

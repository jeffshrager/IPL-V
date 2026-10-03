This directory contains an interpreter which implements a
subset of Information Processing Language-V (IPL-V).
The version of the language implemented is an
approximate subset of
the version described in the second, 1964, edition
of the _Information Processing Language-V Manual_
[MAN1964]
or the
_IPL-V Programmers' Reference Manual_ [MAN1963].
For a description of what is implemented, see
the file `README-SUBSET.md`.

It is possible to use this interpreter to run the code
in the 1963 Stefferud paper on the Logic Theorist [LT1963],
and it appears to successfully reproduce Stefferud's
results.

## How to use

The interpreter is implemented by the Python script
`iplv.py`, which will print out a summary of its
options if invoked with `-h` or `--help`.  The
interpreter only implements a small kernel of IPL-V,
so to use it you must load in libraries along with
the code you wish to interpret.  For example,
to run the program `test.iplv`, the command line
would be:

`python3 iplv.py --extra-syntax lib-ws.iplv --remove-ws lib-simon.iplv lib-misc.iplv --no-remove-ws lib-j100.iplv lib-shuffle-ws.iplv lib-hs.iplv lib-generators-new.iplv lib-at.iplv --no-extra-syntax test.iplv` .

If you prefer to avoid typing this, you can use the shell script `run.sh`:

`sh run.sh test.iplv` .

Since much of the language is implemented in libraries, this interpreter uses many more cycles
than the implementation used by Stefferud in his 1963 paper.  So, to reproduce the results
in Stefferud, you must increase the effort limit, `K22`, to `2100000`.  You can do this by
including the file `redefine-effort.iplv`.  The shell script `test-stefferud.sh`
will run the original Stefferud code together with this file on the input formulae used
in Stefferud's paper; `test-stefferud.out` shows the result of doing this, which
seems to match the results in Stefferud's original paper
quite closely.  Apart from the difference in the effort figures, the
index numbers for rejected subproblems are also different.
This is not surprising as they are internal machine addresses; see line `M079R060` in routine `M79`.

## File list (this directory)

* `README.md` — this file
* `README-SUBSET.md` — describes what is implemented by the interpreter
* Python source implementing the interpreter:
    * `iplparser.py` — parses IPL-V source code
    * `assembler.py` — assembles IPL-V source code into memory
    * `machine.py` — runs the assembled code
    * `util.py` — miscellaneous utility classes and functions, including error reporting
    * `remove_ws.py` — changes IPL-V source code to get rid of the use of temporary W registers
    * `iplv.py` — runnable driver program
* IPL-V source interpreting the language on top of the kernel understood by `machine.py`:
    * `lib-simon.iplv` — library functions implemented by Simon's J's (see <https://computerhistory.org/blog/simons-js/>)
    * `lib-misc.iplv` — other miscellaneous library functions
    * `lib-generators-new.iplv` — J-functions used to make generators, `J17`, `J18`, and `J19`
    * `lib-j100.iplv` — implementation of the generator `J100`
    * `lib-shuffle-ws.iplv` — J-functions `J20` through `J59` used to shuffle around the W registers
    * `lib-at.iplv` — defines the address `@0` to separate library from user code
    * `lib-ws.iplv` — defines W registers
    * `lib-hs.iplv` — defines H registers not already defined in `machine.py`
* Testing:
    * `test.sh`, `test.py` — testing framework.
    * `iplparser.test` — test for `iplparser.py`
    * `remove_ws.test` — test for `remove_ws.py`
    * `iplv.test`, `iplv.usage`, `test-01.iplv`, `test-02.iplv`, `test-03.iplv` — tests for the IPL-V interpreter `iplv.py`
* `run.sh` — convenience shell script to run `iplv.py` together with its libraries
* `redefine-effort.iplv` — file redefining `K22` for greater compatibility with Stefferud's original paper
* `test-stefferud.sh` — convenience shell script to run the Stefferud code (taken from the top-level directory of this repo) on the input used by Stefferud in his paper (also in the top-level directory)
* `test-stefferud.out` — result of running the Stefferud code on his input with this interpreter

## References

[LT1963] _The Logic Theory Machine: A Model Heuristic Program_,
Einar Stefferud,
RAND Research Memorandum RM-3731-CC,
June 1963,
<https://www.rand.org/pubs/research_memoranda/RM3731.html>.

[MAN1963] _IPL-V Programmers' Reference Manual_,
ed. Allen Newell,
RAND Research Memorandum RM-3739-RC,
June 1963,
<https://www.rand.org/pubs/research_memoranda/RM3739.html>.

[MAN1964] _Information Processing Language-V Manual_, second ed., Allen Newell et al., RAND Corporation,
pub.  Englewood Cliffs, NJ: Prentice-Hall, Inc., 1964,
<https://archive.org/details/bitsavers_randiplInfanguageVSecondEdition1964_15001417>.

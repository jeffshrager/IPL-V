It's possible to run the Stefferud 1963 Logic Theorist code [1] in
Rob Storey's IBM 7094 emulator [2], using the version of IPL-V
which it provides.  However, there are four problems to overcome:

1.  The program uses the symbol `'0`, which appears not to be legal
in this version of IPL-V and causes the output of the program
to be garbled.

2. The program is given in two pieces, the first of which
writes itself to tape and is then reloaded.  This is not
necessary.

3. This version of IPL-V doesn't seem to contain the primitives
(J-functions) which the Logic Theorist uses to read in its input.
So, the input expressions must be reformatted into their internal
form and packaged with the program.

4. There is a bug in the program which keeps it from running
successfully at the approximate locations `M016R320` and `M017R300`.
The program gets a level number from subroutine `9-20`, copies
it, and wishes to use `J11` to place it as the attribute `Q17` of the
problem in `W4`.  `J11` takes its arguments in the order (starting
at the top of the stack) as attribute, value, and finally
the list to assign the property of, but the program incorrectly
places the contents of `W4` on top of the stack, followed by
`Q17` and the level number.  The program should be changed
to reshuffle these into the correct order (`Q17`, level number,
current value of `W4`.)

Problem 1 can be solved by removing the use of `'0`,
2 by removing some headers, and
4 by patching the bug.  Also, because of problem 3, you
must remove the header which runs the original executive,
top-level, program.  I have supplied a patch
to make these changes.  For problem 3, you need to
add the input expressions to the program and write
a new executive program to process them, which I have written a
Python script to do.  I have also supplied the result of applying
these changes to Stefferud's code, using the input formulae in
Stefferud's 1963 paper.  To use different input formulae you
should reapply the patch and rerun the script.

The easiest way to run the Logic Theorist is to use the
demonstration script provided with the emulator.
You can copy the Logic Theorist IPL-V code into the `Files\Cards`
subdirectory of the emulator, giving it the name `Sample.Ipl`
(overwriting the sample already there),
start the emulator, and, in the demonstration script, select
"NEW! Try the University of Maryland MAMOS system",
"Run standard IBSYS jobs using the Bamberger system",
and "Run a sample IPL-V job".
Of course, you could also modify the script or use some
other method.

The result of running this code seems to be very similar to
the results in Stefferud's original 1963 paper.  The main
change is that the output lines are truncated; their length
seems to be limited to between 67 and 71 characters.  Also,
the effort limit prints out incorrectly as `000000`
(the actual effort also sometimes prints out like this),
and the actual effort numbers are slightly
different.  The index numbers for rejected subproblems are
also different.  This is not surprising as they are
internal machine addresses; see line `M079R060` in routine
`M79`.

## File list (this directory)

* `README.md` — this file
* `logic-theorist-patch.txt` — Patch for the Stefferud version of the Logic Theorist
* `logictoiplv.py` — Python script to take logical formulae and reformat them into the internal form used by the Stefferud Logic Theorist program; also writes a top-level program to process them
* `make-changes.sh` — Shell script to patch the code and append the output of the Python script
* `patched-logic-theorist.iplv` — Result of patching the original Stefferud code (in the top-level directory of this repo) and appending the processed version of the input formulae used in his paper (also in the top-level directory.)
* `patched-logic-theorist.out` — Result of running the modified Stefferud code on the IBM 7094 emulator.

## References

[1]:
_The Logic Theory Machine: A Model Heuristic Program_,
Einar Stefferud,
RAND Research Memorandum RM-3731-CC,
June 1963,
<https://www.rand.org/pubs/research_memoranda/RM3731.html>.

[2]:
B7094, <https://github.com/Bertoid1311/B7094>.  Windows-based
emulator for the IBM 7094.

The purpose of this repo is to enable the user to run again a late version of
the computer program the Logic Theorist, also called the Logic Theory Machine,
which was originally written by Allen Newell,
J. C. Shaw, and Herbert Simon; this particular version of the Logic
Theorist was published
in a RAND research memorandum in 1963 by Einar Stefferud.
It was written in the language Information Processing Language V (IPL-V)
[14, Summary, p. v].

## About the Logic Theorist

The Logic Theorist was a program which derived proofs of formulae in
propositional logic.  It was
written by Newell, Shaw, and Simon
in order to research heuristic methods and was
part of their research on what they called complex information processing, which was
Newell and Simon's term for what others have called artificial intelligence.
It's been called the first working AI program.  Early versions of the Logic Theorist
were simulated by hand; according to Simon, the first machine-generated proof
from the Logic Theorist came in August 1956
[2, pp. xxvi, 115, 126], [3], [13].

According to Newell and Simon, the heuristics in the Logic Theorist came from the
authors' introspection, rather than from empirical observation of human
behavior  [6, p. 17], [4, p. 154].
However, in 1958 they proposed it as a model of human problem solving [4].
After observing human subjects they decided that its heuristics
should be revised in order to select methods based on the differences
between the existing state and the final state.  These ideas later
became the basis for their General Problem Solver system, which superseded
the Logic Theorist [1, p. 25], [5], [6, pp. 19 ff.].

## About this version of the Logic Theorist

The first version of the Logic Theorist implemented by machine was written in
the programming language IPL-II; it was converted to IPL-V
by Fred Tonge, and later rewritten as a pedagogical model program,
to be used for teaching IPL-V, by Einar Stefferud.  This is the
version used in this repo.
[14, p. 1, Introduction]

This version of the Logic Theorist tries to prove propositional logic
formulae which are built out of variables using the binary
connectives AND, OR, IMPLIES, and EQUIVALENT TO (the biconditional),
and the unary connective NOT.
It works
backwards and tries to use rules of inference to reduce problems,
either to known axioms and theorems, or
to subproblems which then also have to be proven.
The rules of inference used are:
* substitution of expressions for variables;
* replacement of a complete expression by its definition, or vice-versa;
* replacement of a subexpression by its definition, or vice-versa (split into two methods in the program);
* detachment (modus ponens), inference of B from A and A ⊃ B.  A ⊃ B is required to be proven immediately by substitution and A becomes a new subproblem;
* and forward and backward chaining, inference of A ⊃ C from A ⊃ B and B ⊃ C.  This is split into two methods depending on which one of A ⊃ B and B ⊃ C is proven immediately by substitution and which one is taken as a new subproblem [14, Sections 2-6].

Unfortunately, the implementation of the chaining methods was not correct,
meaning that this version of the Logic Theorist does not always produce
valid proofs.

## About IPL-V

Like other languages in the IPL series, IPL-V has the form of an
assembler language for an abstract machine 
[12, p. xiv];
for IPL-V this machine is
a stack machine, and has a memory consisting of words each of
which can hold an ordered pair of pointers
[12, Part 2, Section 1, pp. 135-145]. 
In this way it's similar to LISP.  The main differences from LISP are:

* IPL-V is a low-level assembler language and not functionally oriented.
* There is no automatic memory management or garbage collection.
* The stack orientation means a much greater use of destructive list operations.
* There is no real notion of atoms versus CONS cells (almost everything is an ordered pair.)

IPL-V was first implemented for the IBM 650 early in 1958 [10]
and later implemented for the IBM 704 and various other machines.

The developers published a detailed manual for IPL-V, which went through
two editions  [9], [12].  Both are divided into tutorial and
reference sections.  The tutorial section of the first edition and
the reference sections of both editions were also published separately
[7], [8], [11].

## How to use this repo

There are two ways you can run the Stefferud version of the Logic Theorist.

1.  You can run it on Rob Storey's IBM 7094 emulator.  This requires
fixing some bugs in Stefferud's code and working around some limitations
in the version of IPL-V available in this emulator.
See the subdirectory `7094` for how to do this.

2.  You can run it on a new IPL-V interpreter, written in Python.  See the subdirectory
`interpreter` for how to do this.

## File and directory list

* `README.md` — this file
* `logic-theorist-1963-stefferud.iplv` — source code for the
version of the Logic Theorist in [14].  It was transcribed
by Rupert Lane and Jeff Shrager; see the files `LT/LT.txt` in the
repo <https://github.com/rupertl/iplv-listings> and
`LT/LT7094.iplv` in the repo <https://github.com/jeffshrager/IPL-V>.
This version of the code has had some corrections applied to these
transcriptions.
In [14], this code is in section XV, pp. 129-184,
and section XII, pp. 71-73.

* `logic-theorist-1963-stefferud-input.txt` — input formulae used
for the run of the Logic Theorist in [14].  They were
transcribed from p. 73 of section XII of [14].  Stefferud
also has a third section of input formulae following the sections of
axioms and theorems to prove, but I haven't transcribed it as it's
ignored by the program.

* `logic-theorist-1963-stefferud-output.txt` — output from
the run of the Logic Theorist in [14], transcribed from
pp. 82–107 of section XII of [14].

* `logic-theorist-chapter-2-input.txt` — input formulae for
the definition *1.01, the five propositional logic axioms from *1,
and the theorems from *2 in _Principia Mathematica_

* `logic-theorist-remember-all-theorems-patch.txt` — patch to make
the Logic Theorist remember all theorems it's asked to prove as true,
whether it succeeds in proving them or not

* `7094` — subdirectory explaining how to run this code on Rob Storey's IBM
7094 emulator.

* `interpreter` — subdirectory containing Python re-implementation of IPL-V and explanation of how to run the Stefferud code with it.

## References

[1] In Pursuit of Mind…: The Research of Allen Newell,
John E. Laird and Paul S. Rosenbloom,
_AI Magazine_ **13**, #4, Winter 1992,
pp. 17-45,
DOI [10.1609/aimag.v13i4.1019](https://onlinelibrary.wiley.com/doi/abs/10.1609/aimag.v13i4.1019).


[2] _Machines Who Think: A Personal Inquiry into the History and Prospects of Artificial Intelligence_,
Pamela McCorduck,
2nd edition,
Natick, Massachusetts: A K Peters, Ltd., 2003,
ISBN 1-56881-205-1.


[3] Empirical Explorations of the Logic Theory Machine: a Case Study in Heuristic,
A. Newell, J. C. Shaw, H. A. Simon,
IRE-AIEE-ACM '57 (Western): Papers presented at the February 26-28, 1957, Western joint computer conference: Techniques for reliability,
Feb. 1957,
pp. 218-230,
DOI:
[10.1145/1455567.1455605](https://dx.doi.org/10.1145/1455567.1455605).


[4] Elements of a Theory of Human Problem Solving,
Allen Newell, J. C. Shaw, and Herbert A. Simon,
_Psychological Review_, **65**, #3, 1958,
pp. 151-166.


[5] _The Processes of Creative Thinking_,
Allen Newell, J. C. Shaw, Herbert Alexander Simon,
RAND Paper P-1320,
Sep. 16, 1958, revised Jan. 28, 1959,
presented at a Symposium on Creative Thinking,
Univ. of Colorado, Boulder, Colorado, May 16, 1958,
<https://www.rand.org/pubs/papers/P1320.html>.


[6] _The Simulation of Human Thought_,
A. Newell, H. A. Simon,
RAND Research Memorandum RM-2506,
Dec. 28, 1959,
<https://archive.org/details/bitsavers_randiplRM2umanThoughtDec59_2709419/mode/1up>.


[7] _Information Processing Language V Manual: Section II. Programmers' Reference Manual_,
A. Newell et al., 
RAND Paper P-1918,
March 31, 1960,
available from the 
[CMU Digital Collections](https://digitalcollections.library.cmu.edu/node/1448).


[8] _Information Processing Language V Manual: Section I.  The Elements of IPL Programming_,
A. Newell et al., 
RAND Paper P-1897,
May 16, 1960,
available from the 
[CMU Digital Collections](https://digitalcollections.library.cmu.edu/node/1447).


[9] _Information Processing Language-V Manual_, edited by Allen Newell, RAND Corporation,
pub.  Englewood Cliffs, NJ: Prentice-Hall, Inc., 1961,
available at 
[HathiTrust](https://hdl.handle.net/2027/mdp.39015023105391)
or the
[Stanford Digital Repository](https://purl.stanford.edu/yf916dv1654).


[10] Documentation of IPL-V,
Allen Newell,
_Communications of the ACM_, **6**, #3, March 1963,
pp. 86-89,
DOI [10.1145/366274.366296](https://dx.doi.org/10.1145/366274.366296).


[11] _IPL-V Programmers' Reference Manual_,
ed. Allen Newell,
RAND Research Memorandum RM-3739-RC,
June 1963,
<https://www.rand.org/pubs/research_memoranda/RM3739.html>.


[12] _Information Processing Language-V Manual_, second ed., Allen Newell et al., RAND Corporation,
pub.  Englewood Cliffs, NJ: Prentice-Hall, Inc., 1964,
<https://archive.org/details/bitsavers_randiplInfanguageVSecondEdition1964_15001417>.


[13] Chapter 13, _Models of My Life_,
Herbert A. Simon,
Cambridge, Mass., etc.: MIT Press, 1996 (first pub. 1991, Basic Books.)


[14] _The Logic Theory Machine: A Model Heuristic Program_,
Einar Stefferud,
RAND Research Memorandum RM-3731-CC,
June 1963,
<https://www.rand.org/pubs/research_memoranda/RM3731.html>.

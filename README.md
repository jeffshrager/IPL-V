# Reanimation of LT, The Logic Theorist

---

# Quick start (i.e., what I do):

- Get iplv.lisp into an emacs buffer. (The whole emulator is one file at the moment.)
- Open an emacs shell.
- Start SBCL (no packages required--I think)
- The compile-and-load expr is at the top of the code file: (load (compile-file "iplv.lisp"))
- The exec calls are the end.

There are a couple of warnings that I haven't bothered to fix, but
they don't break it. It'll run two test functions (F1 and
Ackermann). If these don't work, the whole thing wil come to a halt
immediately.

If F1 and Acker pass, then it loads LTFixed.lisp, which is
self-executing. Eventually it'll break, or at least do the wrong thing.

---

# Docs:

The IPL-V manual
(1964-Newell-Information_Processing_Language-V_Second_Edition_1964_OCRED)
and the LT paper (1963_Stefferud_LT_RM-3731_OCRed) are both in here in
PDF, as well as an abbreviate version of the manual called a
"CheatSheet".

# LT Code:

A transcription of the original code, from the Stefferud paper, is here:

[https://docs.google.com/spreadsheets/d/1ibvbyoIT20R4gDqo2iSkk5mJBWsRrtQ6sr8Fj1nz910](https://docs.google.com/spreadsheets/d/1ibvbyoIT20R4gDqo2iSkk5mJBWsRrtQ6sr8Fj1nz910)

This gets pulled down in TSV and run through tsv2lisp.py, basically
just to wrap parens around it, and strip out randomness.

The first column refers to the page in the Stefferud paper from which
this code came. There's a lot of other augmented unreality in the
gsheets that is the mostly to help understand what's going on.

# *IMPORTANT*

LTFixed.lisp is NOT just the latest output from tsv2lisp.py! There
have been lots of little fixes applied (thus the name "LTFixed"). Most
have been documented via lisp-style comments in LTFixed.lisp

# How the emulator works

## Interpretation Cycle

The core of the emulator is IPL-EVAL (which is re-entrant, see J100).

## J-Functions

The built-ins (although they aren't actually built-in, but that's
another story) are called Jfns ... because, you guessed it, they all
start with "J", as "J100", etc. There are many dozens -- probably near
100 -- of these that are used by LT. (I've only bothered implementing
the ones that LT actually uses. In fact, what I call "progress" is
when I get a J-function unimplemented break, because that mean's it go
to a j-function I haven't implemented yet.) In the original IPL-V,
many (perhaps all) of the JFns were actually written in IPL itself. In
fact, we could even probably get them if we wanted to...and maybe we
should, see: [Simon's J
Functions](https://computerhistory.org/blog/simons-js/). But for the
moment I just hack them in Lisp as I get to them. 

# (nearly) Universal stringyness

Instead of numerical addresses the emulator uses strings. (You'd think
that this would be atoms, but it's strings, for a reason I might
remember if I try really hard....hmmm....) Even "0" (as in the end of
a list) is represented as a string, and so all these need to be tested
with string-equal, which is sort of annoying. The only exception is
that actual data numbers, which are stored in the links of cells, are
actual numbers.

# Debugging tools

See examples at the end of iplv.lisp for the moment. You probably at
least want to be running with:
```
(setf *!!list* '(:run :jfns)) 
```
Other options include: :deep-memory :load :run :jfns :run-full :io :end-dump (t for all)

There's are other probably overly-complex debugging tools like a cell
tracer and breaking and stepping facilities.

The *breaks* global var fns let you break at a particular card
ID. Once you've hit a breakpoint *breaks* gets set to t and the thing
is in step mode, where it'll break on every instruction and you use
lisp's :c to step. To continue you set (free!) you can add an arg to
free! that says where to break next (that is, this is setf back to
*breaks*, which, with no arg, gets nil which is just free running.

You can tell the emulator to dump specific registers (and their
stacks) on every step by, e.g.,

```
(setf *trace-cell-names* '("H0" "W0" "W1" "W2") *cell-tracing-on* t)
```

The most useful (and overly complex) facility lets you eval any expr
at a given card ID, for example:

```
(setf *trace-line-id-exprs*
   '(("P052R040"
      (setf *trace-cell-names* '("W0" "W1" "H0") *cell-tracing-on* t)
      (setf *!!list* '(:run :jfns))
      (trace symbolify ipl-meta-string-equal ipl-string-equal)
      )
     ("P052R200" (trace) (setf *cell-tracing-on* nil *!!list* *default-!!list*))
     ("P052R270" (trace) (setf *cell-tracing-on* nil *!!list* *default-!!list*))
     ("P052R490" (trace) (setf *cell-tracing-on* nil *!!list* *default-!!list*))
     ))
```

There are several shorthand convenience fuctions and symbol macros
that dump various info:

rsc, rsc (because I can't remember which order it is!) and rsc* (rsc*)
dump the main registers.

(lpll <a-list-cell-head>) prints out a linear list and its dlist that
that cell is the head of in a faux line-printer format.

---

# Current top issues:

(What we're working through at the moment, to remind ourselves.)

## The H0 cleanup problem

There is a running issue about Jfns popping off things from H0, or
not. Some do, some don't, it's sort of assumed tha they do unless
stated otherwise ... or something. It seems that all JFns are supposed
to remove their inputs, e.g., p.10: "...it is understood from the
definition of TEST that J2 will remove both (0) and (1) from HO."

We get to situations like this where there's nothing left on the H0
stack!

```
!![RUN]::>>>>>>>>>> Calling J155 [Print line] (No Args)
BAD EXPRESSION   K51K51/14I+27707Q+27792K52=+27927K51-+27915/14V+27897Q+27792K52
!![RUN]::@466- >>>>>>>>>> {X001R320::X1+28068/40/H0/X1+28069}
!![RUN]::@467- >>>>>>>>>> {X001R330::X1+28069//J15/X1+28070}
!![RUN]::>>>>>>>>>> Calling J15 [ERASE ALL ATTRIBUTES OF (0)]
   (ARG0)=(NIL)
!![JFNS]::J15 clearing the dl of NIL (NIL)
```

Someplace around @368 H0 seems to get over-popped. I think this expects
the name of the list ("*101") but I'm not sure. The last time we see
that in H0+ is @368:

```
!![RUN]::@368+ >>>>>>>>>> {M079R030::M79+29137//J157/J8 [        ENTER IT, DISCARD (0)./]}
   H0={(000D030::(+30229//K51/0} ++ ("*101")
   W0={W0///} ++ ("W0-empty")
   W1={W1///} ++ ("W1-empty")
   W2={W2///} ++ ("W2-empty")
!![RUN]::>>>>>>>>>> Calling J157 [ENTER DATA TERM (0) LEFT-JUSTIFIED]
   (A0)=({(000D030::(+30229//K51/0})
!![JFNS]::J157 called on {(000D030::(+30229//K51/0}
!![JFNS]::Print buffer is now:
"BAD EXPRESSION   K51                                                            "
   H0="*101" ++ NIL
   W0={W0///} ++ ("W0-empty")
   W1={W1///} ++ ("W1-empty")
   W2={W2///} ++ ("W2-empty")
!![RUN]::>>>>>>>>>> Calling J8 [RESTORE H0] (No Args)
   H0=NIL ++ NIL
   W0={W0///} ++ ("W0-empty")
   W1={W1///} ++ ("W1-empty")
   W2={W2///} ++ ("W2-empty")
```

Something weird is going on with the restores (J8). If you look at the
M79 code it pushes and pops H0 itself, so the J8 restore seems like
over-popping, but someone ahead of all this might have over-popped.

## The character/string/symbol/name mess.

There are a lot of issues around string handling, esp. in the single
character case (which the translator uses a lot!) Like, "A" is
represented as the name/symbol "A0", so the equiv. of IPL string-equal
(called, oddly enough: ipl-string-equal) has to do all sorts of
heuristic bending over backwards, as does the cell "getter" (<== ...)
and (cell< ...) which take either a string (cell name) or cell and
return a cell.

---

# On IPL-V

There's a lot to say about this, but in many ways this is the most
interesting part of all this. I'm just collecting random notes here
for the moment. Many additional notes (grumblings) are dispersed
throughout the lisp code.

## PQ Meaning for all PQ used in LT:

```
00 (blank) Execute fn named by symb name per se (*)
01 Execute fn contained in cell named by symb (*>)
04 (blank) Execute fn named by symb name per se (same as 00 bcs no tracing) (>)
10 Push the symb (name) itself on H0 (*>)
11 Push content of the cell named by symb, onto H0 (*>)
12 Push 2nd deref on H0 (*>>)
14 Push the symb (name) itself on H0 (same as 10 bcs no tracining) (*)
20 Move H0 to the named symbol (per se) and pop (restore) H0. (*)
   (? This is a little weird bcs it seems like you should be moving
      the value to the command itself!)   
21 Move H0 to the cell named by symb, and pop (restore) H0. (*>)
30 Pop the named stack (per se) (*)
31 Pop the stack of the sym in the named cell (1st ref) (*>)
32 Pop the stack of the 2nd derefed cell (*>>)
40 Push down (preserve) the named symb (per se)
50 Replace H0 by the named symb (per se) (*)
51 Replace H0 by the cell named in the H0 symb (*>)
52 Replace H0 2nd deref (*>>)
60 Set the symb name per se to H0 (or cell named by H0 if string) (*)
64 Set the symb name per se to H0 (or cell named by H0 if string) (Same as 60 (no tracing)) (*)
70 Branch to symb name (per se) if H5- (*)
```
## Changes from standard (by the manual) IPL-V

### I/O is *highly* simplified

The whole messy I/O system has been replaced by a single 80-char
buffer called ```*W24-Line-Buffer*``` which gets loaded with stuff to
print, or with the things that get read on the input side. I don't
think that LT will require more than this.

### Only integer arthimetic is implemented

### H5 constains a string: "+" or "-" (as opposed to holding a cell
name: p...something-or-other, as descirbed in the manual).

### In most locations, a string for the name of a cell is
automatically de-refed to the cell (by cell< or <==). The reason there
are two of these is that <== got hypercomplexified by the character
thing, and started dereferencing in weird situations. Sometimes you
need to use (cell ...) instead of (cell< ...) because (cell ...) is a
setf'able macro, whereas cell< is not.

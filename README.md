# Reanimation of Early Simon, Newell, and Shaw IPL-V AIs

---

# Quick start (i.e., what I do):

- Get iplv.lisp into an emacs buffer. (The whole emulator is one file at the moment.)
- Open an emacs shell.
- Start SBCL (no packages required--I think)
- The compile-and-load expr is at the top of the code file: (load (compile-file "iplv.lisp"))

The exec calls are the end. What will run is whatever I happened to be
testing most recently, so t might run LT or EPAM, or something else,
and you're likely to get a bunch of debugging crap.

To run LT, for example, you'll want to be sure that there's no qoute
on this line near the end:

```
(progn ;; LT
    ...
```

That is, it look like the above, not:

```
'(progn ;; LT
```


(The single quote in Lisp blocks execution, so it acts like commenting
out a whole block of code.)

If you want to run the ackermann function instead, or in addition to
this, that call is somewhat above:

```
(progn ;; Ackermann test
```

Just make sure that that one doesn't have a quote.

You'll have to suss out the details of debugging yourself, but if you
want it all turned off, make sure it only has this minimum execution
set:

```
(progn ;; Ackermann test
 (set-default-tracing)
 (setf *!!* '() *cell-tracing-on* nil)
 (load-ipl "SUBIR/CODE.liplv")
 ;; For example: (Ackerman requires much longer than default!)
 ;; (load-ipl "misccode/Ackermann.liplv" :adv-limit 250000) 
 )
```


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

# **IMPORTANT**

**LTFixed.lisp is NOT just the latest output from tsv2lisp.py! There
have been lots of little fixes applied (thus the name "LTFixed"). Most
have been documented via lisp-style comments in LTFixed.lisp**

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

**WWW Warning!** Beware of Jfns that pop their args and then instead of
PUSHING (ipush "H0" ...) the result, they just setf (H0) to the
result. THIS IS VERY LIKELY TO LOSE A STACK ENTRY BY ACCIDENTALLY
OVERWRITING! (As soon as I wrote the above, I went back and looked at
my early Jfns and immeditely found a case of this that was f'ing the
whole thing!)

# (nearly) Universal stringyness

Instead of numerical addresses the emulator uses strings. Even "0" (as
in the end of a list) is represented as a string, and so all these
need to be tested with string-equal, which is sort of annoying. The
only exception is that actual numerical data, which are stored in the
links of cells, are actual numbers.

You'd think that this would be atoms, but it's strings, for a reason I
might remember if I try really hard....hmmm....Oh, right, it's because
a LOT of the symbols used LT would be illegal as atoms, like |(0| or
|./|. The original IPL-V compilers turned everything into addresses,
so this wasn't an issue. (Maybe I should have actually gone down that
path...?)

# Debugging tools

See examples at the end of iplv.lisp for the moment. You probably at
least want to be running with:

```
(setf *!!* '(:run :jfns)) 
```

Other options include: :jdeep :jfns :run :jcalls :dr-memory :s :run-full :deep-alerts :load

:run output looks like this:

```
@24528+ >>>>> {P055R170::P55-9-2||J60|P55+1676 [SET UP CELL HOLDING SUBLIST.;]} (Execute fn named by symb name itself)
```

The @nnn is the value of H3 -- the interpreter cycle counter. The +
(or -) immediately after the cycle count is the value of H5 (the test
result register). The >>> is just so you can find these lines, and the
{...} is the print out of the cell. The [...] is the comment from the
instruction. The thing at the end is a convenience that tells you what
the PQ means. This comes from the PQ table below.

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
  (setf *trace-@orID-exprs*
	'((23750 (setf *!!* '(:run :jcalls :jfns :jdeep) *trace-cell-names-or-exprs* '("H0" "W0" "W1" "W2") *cell-tracing-on* t))
	  (2000 (break))
	  ("P052R040"
	    (setf *trace-cell-names* '("W0" "W1" "H0") *cell-tracing-on* t)
            (setf *!!* '(:run :jfns))
            (trace symbolify ipl-meta-string-equal ipl-string-equal)
           )	     
          ("P052R200" (trace) (setf *cell-tracing-on* nil *!!* *default-!!list*))
          ("P052R270" (trace) (setf *cell-tracing-on* nil *!!* *default-!!list*))
          (123 (trace) (setf *cell-tracing-on* nil *!!* *default-!!list*))
     ))
```

In the above, the string "ID" (as "P052R270") can be a number instead,
in which case it takes place when the (H3) cycle counter hits the
indicated value (as the 123 example, above). Note that (trace) is just
a call to the Lisp TRACE function, so you can strategically turn
on/off lisp tracing at specific machine cycles. 

There are several shorthand convenience fuctions and symbol macros
that dump various info:

rsc, rsc (because I can't remember which order it is!) and rsc* (rsc*)
dump the main registers.

(pll <a-list-cell-head>) prints out a linear list and its dlist that
that cell is the head of, and (pl ...) prints complex lists
recursively with indentation.


---

# (See notes.txt for current top issues.)

---

# On IPL-V

There's a lot to say about this, but in many ways this is the most
interesting part of all this. I'm just collecting random notes here
for the moment. Many additional notes (grumblings) are dispersed
throughout the lisp code.

## PQ Meaning for all PQ used in LT:

```
    ("" "Execute fn named by symb name itself")
    ("  " "Execute fn named by symb name itself")
    ("00" "Execute fn named by symb name itself")
    ("01" "Execute fn in cell named by symb")
    ("04" "Execute fn named in symb name itself (==00)")
    ("10" "Push the symb (name) itself on H0")
    ("11" "Push cntnts of the cell named by symb, onto H0")
    ("12" "Push 2nd deref on H0")
    ("13" "Push the symb (name) itself on H0 (==10)")
    ("14" "Push the symb (name) itself on H0 (==10)")
    ("20" "Move H0 to the named symbol itself and pop H0")
    ("21" "Move H0 to the cell named by symb, and pop H0")
    ("30" "Pop the named stack itself")
    ("31" "Pop the stack of the sym in the named cell")
    ("32" "Pop the stack of the 2nd derefed cell")
    ("40" "Push down (preserve) the named symb itself")
    ("50" "Replace H0 by the named symb itself")
    ("51" "Replace H0 by the cell named in the H0 symb")
    ("52" "Replace H0 2nd deref")
    ("60" "Copy of (0) replaces S; S lost; H0 n.c.")
    ("64" "Copy of (0) replaces S; S lost; H0 n.c. (==60)")
    ("70" "Goto by H5: -symb|+link itself")
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

### There are like six ways to deref a stringp symbol to a cell,
including (<== ...) (CELL ...) (<=! ...), and you can just do it the
hard way: (gethash ... *symtab*) although that could return an
unprotected nil. The reason for this is mostly that I just evolved
more and more complex means of doing this, and then devolved them into
simple and simpler means as I understood better what was going
on. This is one of the many places that would get unified in a
refactor/rewrite.

In most locations, a string for the name of a cell is automatically
de-refed to the cell (by CELL or <==). The reason there are two of
these is that <== got hypercomplexified by the character thing, and
started dereferencing in weird situations. Sometimes you need to use
(CELL ...) instead of (<== ...) because (CELL ...) is a setf'able
macro, whereas <== is not. (See "The character/string/symbol/name
mess." above.)

Another reason I didn't just use the Lisp symbol table, but created my
own memory system using strings instead of atoms, is that this way I
have complete control of what's going on. I've run into issues before
when using the Lisp symbol table with reserved atoms and such-like. I
can usually get around most of those, sometimes by disintering them,
and other radical hacks, but, like, I really didn't want to have to
break the Lisp system, and at the same time make it non-transportable.


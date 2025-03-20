# Reanimation of LT, The Logic Theorist

## Quick start (i.e., what I do):

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

## Current top issue:

(Notes about what we're working through at the moment.)

## Docs:

The IPL-V manual
(1964-Newell-Information_Processing_Language-V_Second_Edition_1964_OCRED)
and the LT paper (1963_Stefferud_LT_RM-3731_OCRed) are both in here in
PDF, as well as an abbreviate version of the manual called a
"CheatSheet".

## LT Code:

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

## How the empulator works.

# Interpretation Cycle

The code of the emulator is IPL-EVAL (which is re-entrant, see J100).

# J-Functions

The built-ins (although they aren't actually built-in, but that's
another story) are called Jfns ... because, you guessed it, they all
start with "J", as "J100", etc. There are many dozens -- probably near
100 -- of these that are used by LT. (I've only bothered implementing
the ones that LT actually uses. In fact, what I call "progress" is
when I get a J-function unimplemented break, because that mean's it go
to a j-function I haven't implemented yet.) In the original IPL-V,
many (perhaps all) of the JFns were actually written in IPL itself. In
fact, we could even probably get them if we wanted to...and maybe we
should, see: [Simon's J Functions](https://computerhistory.org/blog/simons-js/)

# Debugging tools



## On IPL-V

There's a lot to say about this. We can just collect random notes here
for the moment.
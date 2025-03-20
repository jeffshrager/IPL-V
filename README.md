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

## 

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

# IMPORTANT

LTFixed.lisp is NOT just the latest output from tsv2lisp.py! There
have been lots of little fixes applied (thus the name "LTFixed"). Most
have been documented via lisp-style comments in LTFixed.lisp
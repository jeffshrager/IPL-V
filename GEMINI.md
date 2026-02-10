=================== GENERAL DETAILS =================== 

This is The Logic Theory Macine. It is described in:

  1963_Stefferud_LT_RM-3731_OCRed.pdf

The program is written in IPL-V. The IPL-V manual is:

  1964-Newell-Information_Processing_Language-V_Second_Edition_1964_OCRED.pdf

IPLV.lisp is a IPL-V interpreted written in Lisp.

The way that you run LT is this:

  rm iplv.out; sbcl --lose-on-corruption --eval '(progn (load (compile-file "iplv.lisp")) (backtrace))' >> iplv.out

This will create an output file called "iplv.out" which you can analyze.

The last expression in iplv.lisp runs LT. The LT IPL-V code is in:

  LTFixed.liplv

Note that after the "type 5" expression near the end:

  ("KICK OFF FOR PROVING THEOREMS" "5" "" "" "" "X1" "" "" "")

There are two sets of expressions in the LT logical syntax, for example:

*1.21  ((AVB)IA)
*1.22  ((AVB)I(BVA))
[then a blank line]
*2.92   ((PVQ)IQ)

In the LT language, I represents implication (usually rightarrow), V
is OR, * is AND, - is NOT, = is equal, and .=. is equal by definition.

The first set (1.21, 1.22, and possibly other before the blank line)
are axioms, and the latter set (2.92, and possibly others) are
theorems to be proved through the axioms.

When ILPV.lisp is loaded, the last expression:

  (progn ;; LT 
    ...
    (load-ipl "LTFixed.liplv" :adv-limit 500000)
    )

sets up the trace/dump/debugging globals, and then load and runs the
LT code.

Generally you don't wantto worry about the :adv-limit, we're not going
to get anywhere near there.

You will usually want to use this syntax to adjust what you're seeing in iplv.out:

  (2600
    (setf *!!* '(:run :jcalls) *cell-tracing-on* t) ;; :s :run-full :jcalls :alerts :dr-memory :gentrace
    (setf *trace-cell-names-or-exprs* '("H0" "W0" "W1""W2") *cell-tracing-on* t)  ;;    "W0" "W1" "W2" "W3"	
    (trace J2n=move-0-to-n-into-w0-wn ipop ipush)
    )

The first is the (enulated) machine cycle at which this will
execute. This can also be a card ID, as, for example:

  ("M088R020" ...

(The key can be partial, as "P052R")

or an arbitrary expression.

  ((zerop (mod (h3-cycles) 100)) (print (h3-cycles)))

This latter one prints the cycle counter (H3) every 100 cycles. This
is sometime useful for finding a place ot put a break.

A useful expression is:

  (pl "symbol")

This prints a list bount to the indicateed symbol. (Symbols with
dashes, e.g., "9-1234" are local to the list they are in. All other
symbols are global. (pl ...) will work with either.)

You usually do NOT want to do a full trace, that is, for example:

  (0
    (setf *!!* '(:run :jcalls) *cell-tracing-on* t) ;; :s :run-full :jcalls :alerts :dr-memory :gentrace
    (setf *trace-cell-names-or-exprs* '("H0" "W0" "W1""W2") *cell-tracing-on* t)  ;;    "W0" "W1" "W2" "W3"	
    )

because this will be much too much output.

You should start perhaps by doing a full call-only trace, as:

  (0
    (setf *!!* '(:run :jcalls) *cell-tracing-on* t)
    )


then once you have an idea where to start, you can add more detail and
break at some point to save output size (and analytical time!) for
example:

  ...
  (1234
    (setf *!!* '(:run :jcalls) *cell-tracing-on* t) 
    (setf *trace-cell-names-or-exprs* '("H0" "W0" "W1""W2") *cell-tracing-on* t)
    )

  (1250 (break))
  ...

You may thinkg that you've found a bug in the LT code (that is, in
LTFixed.liplv). This is almost never the case. Almost all of the
problems are bugs in my J function definitions (defj ... and
associated helpers). 

=================== CURRENT PROBLEM =================== 

These axioms:

*1.21  ((AVB)IA)
*1.22  ((AVB)I(BVA))

Should be able to easily prove this theorem:

*2.92   ((PVQ)IQ)

The output we current get is:

:::::::::::::::::::::::::::::::: 1.21    (AVB)IA                                                                 
:::::::::::::::::::::::::::::::: 1.22    (AVB)I(BVA)                                                             
::::::::::::::::::::::::::::::::                                                                                 
::::::::::::::::::::::::::::::::                                                                                 
:::::::::::::::::::::::::::::::: 2.92    (PVQ)IQ                                                                 
:::::::::::::::::::::::::::::::: TO PROVE                                                                        
:::::::::::::::::::::::::::::::: 2.92    (PVQ)IQ                                                                 
::::::::::::::::::::::::::::::::            .0   ((PVQ)IQ)VB              1.21  ,0 DETACHMENT                    
::::::::::::::::::::::::::::::::            .0   (PVQ)I(((PVQ)IQ)VB)  1.21  ,0 BACKWARD CHAINING                 
:::::::::::::::::::::::::::::::: NO PROOF FOUND                                                                  
::::::::::::::::::::::::::::::::                                                                                 
::::::::::::::::::::::::::::::::                                                                                 
:::::::::::::::::::::::::::::::: EFFORT              LIMIT 20000         ACTUAL 0                                
:::::::::::::::::::::::::::::::: SUBPROBLEMS         LIMIT               ACTUAL                                  
:::::::::::::::::::::::::::::::: SUBSTITUTIONS       LIMIT               ACTUAL                                  

Problem: Why is no proof found?


;;; (load "igraph.lisp")
;;; dot -Tpng graph.dot -o graph.png

(defparameter *names*
  '((turing "Turing" "springgreen")
    (turing-machine "Turing Machine" "cyan")
    (mccarthy "McCarthy" "springgreen")
    (mind-paper "1950 Mind Paper" "cyan")
    (godel "Godel" "springgreen")
    (slip "Slip" "cyan")
    (lisp "Lisp" "cyan")
    (lambda-calculus "Lambda Calculus" "cyan")
    (turing-test "Turing test (Immitation Game)" "cyan")
    (hilbert-problem "Hilbert's problem"  "magenta")
    (church "Church" "springgreen")
    (hilbert "Hilbert" "springgreen")
    (p-m "Principia Mathematica" "cyan")
    (nss "Newell/Simon/Shaw" "springgreen")
    (lt "Logic Theory Machine" "cyan")
    (ipl-v "IPL-V" "cyan")
    (weizenbaum "Weizenbaum" "springgreen")
    (eliza1 "MAD-SLIP ELIZA" "cyan")
    (cosell "Bernie Cosell" "springgreen")
    (eliza2 "Lisp ELIZA" "cyan")
    (invented "Invented")
    (addressed "Addressed")
    (published "Published")
    (described "Described")
    (quoted "Quoted")
    (influenced "Influenced")
    (replaced "Replaced")
    (first-implemented "First-implemented")
    (ada "Ada Lovelace" "springgreen")
    (symbolic-computing "Symbolic Computing" "magenta")
    (flpl "FLPL" "cyan")
    (implemented-in "Implemented in")
    (f-p "Functional Programming"  "magenta")
    (based-upon "Based upon")
    (set-theory "Set theory" "magenta")
    (lists "Lists" "magenta")
    ))

(defparameter *force-left* '(hilbert p-m hilbert-problem ada))
(defparameter *force-right* '(eliza1 eliza2))

(defparameter *graph* 
  '((turing invented turing-machine)
    (lt implemented-in ipl-v)
    (eliza1 implemented-in slip)
    (eliza2 implemented-in lisp)
    (turing-machine addressed hilbert-problem)
    (turing published mind-paper)
    (mind-paper described turing-test)
    (eliza1 addressed turing-test)
    (mind-paper quoted ada)
    (hilbert invented hilbert-problem)
    (hilbert-problem influenced turing)
    (hilbert-problem influenced godel)
    (eliza1 influenced eliza2)
    (set-theory influenced godel)
    (hilbert-problem influenced church)	
    (set-theory influenced lists)
    (lists influenced ipl-v)
    (p-m influenced hilbert)
    (p-m influenced nss)
    (p-m based-upon set-theory)
    (church invented lambda-calculus)
    (lambda-calculus influenced mccarthy)
    (lambda-calculus addressed hilbert-problem)
    (lambda-calculus implemented f-p)
    (mccarthy invented lisp)
    (lisp replaced slip)
    (weizenbaum invented slip)
    (weizenbaum implemented eliza1)
    (cosell implemented eliza2)
    (lisp influenced cosell)
    (ada invented symbolic-computing)
    (symbolic-computing influenced ipl-v)
    (symbolic-computing influenced lisp)
    (f-p influenced mccarthy)
    (ipl-v influenced mccarthy)
    (ipl-v influenced slip)
    (ipl-v influenced lisp)
    (mccarthy influenced flpl)
    (flpl influenced slip)
    (nss implemented lt)
    (nss implemented ipl-v)
    (lt implemented p-m)))

;;; ------------------------------------------------------------
;;; Confirm name coverage and export Graphviz DOT if consistent.
;;; ------------------------------------------------------------

(defun lookup-name (sym)
  "Return two values for SYM from *names*: display-name (string) and color (or NIL)."
  (let ((rec (assoc sym *names* :test #'eq)))
    (values (and rec (second rec))
            (and rec (third rec)))))

(defun graph-missing-names ()
  "Return list of node symbols (src/dst) in *graph* that lack entries in *names*."
  (let ((nodes (remove-duplicates
                (loop for (src rel dst) in *graph* append (list src dst))
                :test #'eq)))
    (remove-if (lambda (s) (nth-value 0 (lookup-name s))) nodes)))

(defun export-graph-to-dot (&optional (filename "graph.dot"))
  "Write DOT if all nodes in *graph* have names in *names*.
Returns T on success, NIL if missing names."
  (let ((missing (graph-missing-names)))
    (if missing
        (progn
          (format t "~&ERROR: Missing name definitions for: ~{~A~^, ~}~%" missing)
          nil)
	(let* ((edges *graph*)
	       (graph-nodes (remove-duplicates
			     (loop for (s r d) in edges append (list s d))
			     :test #'eq))
	       (forced (remove-duplicates
			(append *force-left* *force-right*)
			:test #'eq))
	       (all-nodes (remove-duplicates
			   (append graph-nodes forced)
			   :test #'eq)))
	  (with-open-file (out filename
			       :direction :output
			       :if-exists :supersede
			       :if-does-not-exist :create)
	    (format out "digraph G {~%  rankdir=LR;~%  graph [splines=true];~%  node [shape=ellipse];~%~%")

	    ;; --- Node declarations (names + optional fillcolor) ---
	    (dolist (sym all-nodes)
	      (multiple-value-bind (nm color) (lookup-name sym)
		(if color
		    (format out "  ~S [style=filled, fillcolor=~S];~%" nm color)
		    (format out "  ~S;~%" nm))))

	    (format out "~%")
	    ;; --- Edges ---
	    (loop for (src rel dst) in edges
		  for sname = (nth-value 0 (lookup-name src))
		  for dname = (nth-value 0 (lookup-name dst))
		  do (format out "  ~S -> ~S [label=~S];~%"
			     sname dname (string-downcase (symbol-name rel))))

	    ;; --- Force-left (rank=min) ---
	    (when *force-left*
	      (format out "~%  { rank=min; ")
	      (dolist (sym *force-left*)
		(let ((nm (nth-value 0 (lookup-name sym))))
		  (when nm (format out "~S " nm))))
	      (format out "; }~%"))

	    ;; --- Force-right (rank=max) ---
	    (when *force-right*
	      (format out "~%  { rank=max; ")
	      (dolist (sym *force-right*)
		(let ((nm (nth-value 0 (lookup-name sym))))
		  (when nm (format out "~S " nm))))
	      (format out "; }~%"))

	    (format out "}~%")))
	)))

(export-graph-to-dot "graph.dot")

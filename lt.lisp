;;; lt.lisp — Logic Theorist runner for the IPL-V interpreter
;;;
;;; This file loads the generic IPL-V interpreter (iplv.lisp) and adds
;;; all LT-specific analysis: proof-graph generation, M19 annotation,
;;; subroutine trace hooks, and the LT execution call.
;;;
;;; Run with:
;;;   rm iplv.out; sbcl --lose-on-corruption \
;;;     --eval '(progn (load (compile-file "lt.lisp")) (backtrace))' >> iplv.out

;;; Load the generic interpreter first.
(load (compile-file "/Users/jeffshrager/Desktop/AIHistory/IPL-V/repo/iplv.lisp"))

;;; Directory where per-run log and dotstar files are written.
(defparameter *lt-results-dir*
  "/Users/jeffshrager/Desktop/AIHistory/IPL-V/repo/ltresults"
  "Root directory for LT run logs and dotstar files.")

;;; When bound to an open stream, proof-graph! tees all DOT output there
;;; in addition to the individual per-theorem .dot file.
(defvar *lt-dotstar-stream* nil)

;;; =========================================================================
;;; Proof graph generator (for theorem 4.25 or any bounded execution window)
;;;
;;; Usage: set up *trace-exprs* to clear *card-cycles.ids-executed* at the
;;; start of the proof of interest, then call (proof-graph!) at the end.
;;; Requires the :ascend entries to be (list :ascend (H5)) -- see ASCEND label.

(defparameter *proof-graph-methods*
  '(("M001" . "M1:Executive")
    ("M007" . "M7:ApplyMethods")
    ("M008" . "M8:MakeMethodList")
    ("M011" . "M11:Detachment")
    ("M012" . "M12:Substitution")
    ("M013" . "M13:Replacement")
    ("M014" . "M14:FwdChain")
    ("M015" . "M15:BwdChain")
    ("M016" . "M16:SublvlRepl-A")
    ("M017" . "M17:SublvlRepl-B")
    ("M019" . "M19:Derivation")   ; assigned by annotate-m19-node! using W0/W1
    ("M060" . "M60:FindNextProb")
    ("M070" . "M70:TryMethods")
    ("M090" . "M90:CheckLimits"))
  "Alist of (4-char-prefix . display-label) for major LT proof methods.")

;;; M19 annotation: populated by *trace-exprs* at M019R010 (after J53 sets W0/W1).
;;; Key = cycle of M019R000, value = (thm-name method-name).
(defvar *m19-annotations* (make-hash-table :test #'equal))
(defvar *m19-r000-cycle* nil)

(defun m19-thm-pretty (raw)
  "Format *401 → *4.01, *12 → *1.2, *208 → *2.08 etc."
  (if (and (stringp raw) (> (length raw) 2) (char= (aref raw 0) #\*))
      (let* ((digits (subseq raw 1))
             (n (length digits))
             (split (max 1 (- n 2))))
        (format nil "*~a.~a" (subseq digits 0 split) (subseq digits split)))
      raw))

(defun proof-graph! (&optional (filename "/tmp/proof.dot") (thm-label "Problem"))
  "Walk *card-cycles.ids-executed* and emit a Graphviz DOT call graph of
   the major proof method invocations.  THM-LABEL is used for the root node
   and the DOT file comment (e.g. \"Problem *4.25\").
   Node colors: green=H5+, pink=H5-, yellow=unknown.
   Edges run from caller to callee.
   Render with: dot -Tpdf FILE.dot -o FILE.pdf"
  (let* ((entries (reverse *card-cycles.ids-executed*)) ; chronological order
         (depth 0)
         (all-nodes nil)   ; plists accumulated in reverse order, reversed at end
         (node-stack nil)  ; stack of plists for currently open major-method frames
         (node-counter 0))
    (loop for entry in entries do
      (cond
        ;; Entering a subroutine (any subroutine, not just major ones)
        ((eq entry :descend)
         (incf depth))
        ;; Returning from a subroutine; entry is (:ascend h5-string)
        ((and (listp entry) (eq :ascend (car entry)))
         (let ((h5 (second entry)))
           ;; If the top frame on our major-method stack is at this depth,
           ;; record its outcome and pop it.
           (when (and node-stack
                      (= (getf (first node-stack) :depth) depth))
             (setf (getf (first node-stack) :h5) h5)
             (pop node-stack)))
         (decf depth))
        ;; Card execution entry: (cycle . card-id-string)
        ;; Detect R000 entry points of major proof methods.
        ((and (listp entry) (stringp (cdr entry))
              (>= (length (cdr entry)) 4)
              (search "R000" (cdr entry) :test #'char-equal))
         (let* ((id (cdr entry))
                (cycle (car entry))
                (mpair (find (subseq id 0 4) *proof-graph-methods*
                             :key #'car :test #'string-equal)))
           (when mpair
             (let* ((m19-ann (and (string-equal (car mpair) "M019")
                                  (gethash cycle *m19-annotations*)))
                    ;; m19-ann = (thm-name method-name), e.g. ("*401" "M13")
                    ;; W0 gives short name "M13"; keys are "M013", so pad.
                    (label (if m19-ann
                               (let* ((meth (second m19-ann))
                                      (meth-key (if (and (> (length meth) 1)
                                                         (char= #\M (aref meth 0)))
                                                    (format nil "M0~a" (subseq meth 1))
                                                    meth))
                                      (meth-label (or (cdr (assoc meth-key *proof-graph-methods*
                                                                   :test #'string-equal))
                                                      meth)))
                                 (format nil "~a\\n~a" meth-label (m19-thm-pretty (first m19-ann))))
                               (cdr mpair)))
                    (node (list :node-id    node-counter
                                :method     (car mpair)
                                :label      label
                                :cycle      cycle
                                :depth      depth
                                :parent-id  (when node-stack
                                              (getf (first node-stack) :node-id))
                                :h5         nil)))
               (push node all-nodes)
               (push node node-stack)
               (incf node-counter)))))))
    ;; Reverse to get chronological (oldest-first) order
    (setq all-nodes (reverse all-nodes))
    ;; ipl-eval now pushes :descend at entry so depth tracking works for
    ;; J100/J1/J18 calls too.  Any remaining orphan nodes (e.g. the very
    ;; first ipl-eval call whose :descend was cleared by *trace-exprs*)
    ;; get a synthetic root node so the graph has a single root.
    (let* ((root-id node-counter)
           (root-node (list :node-id   root-id
                            :method    "ROOT"
                            :label     thm-label
                            :cycle     0
                            :depth     -1        ; above everything
                            :parent-id nil
                            :h5        "+")))    ; proof ultimately succeeded
      (incf node-counter)
      (loop for node in all-nodes do
        (when (null (getf node :parent-id))
          (setf (getf node :parent-id) root-id)))
      (push root-node all-nodes)) ; root first in the list for DOT output
    ;; Print indented text summary to stdout
    ;; (format t "~%Proof graph: ~a major-method invocations captured.~%" (1- (length all-nodes)))
    '(loop for node in (rest all-nodes) do   ; skip synthetic root in text dump
      (format t "~v@T~a  cycle=~a  h5=~a~%"
              (* 2 (max 0 (getf node :depth)))
              (getf node :label)
              (getf node :cycle)
              (or (getf node :h5) "?")))
    ;; Write DOT file (and tee to *lt-dotstar-stream* if bound).
    (with-open-file (file-out filename :direction :output :if-exists :supersede)
      (let ((out (if *lt-dotstar-stream*
                     (make-broadcast-stream file-out *lt-dotstar-stream*)
                     file-out)))
      (format out "// Proof-method call graph: ~a~%" thm-label)
      (format out "// Generated by (proof-graph!) in lt.lisp~%")
      (format out "digraph \"~a\" {~%" thm-label)
      (format out "  rankdir=TB;~%")
      (format out "  node [shape=box, fontname=\"Courier\", style=filled, fontsize=10];~%")
      (format out "  edge [color=gray40, fontsize=8];~%")
      ;; Nodes
      (loop for node in all-nodes do
        (let ((nid   (getf node :node-id))
              (label (getf node :label))
              (cycle (getf node :cycle))
              (h5    (getf node :h5))
              (root? (equal (getf node :method) "ROOT")))
          (if root?
              (format out "  N~a [label=\"~a\", shape=ellipse, fillcolor=\"#ADD8E6\"];~%"
                      nid label)
              (format out "  N~a [label=\"~a\\ncycle ~a\", fillcolor=~a];~%"
                      nid label cycle
                      ;; M19 (derivation/sub-problem) nodes use gold/gray rather
                      ;; than green/pink, because H5 means "sub-problem accepted"
                      ;; not "theorem proved" -- avoiding misleading colors.
                      (if (string-equal (getf node :method) "M019")
                          (cond ((equal h5 "+") "\"#FFD700\"") ; gold  = sub-problem queued
                                ((equal h5 "-") "\"#D3D3D3\"") ; gray  = sub-problem rejected
                                (t              "\"#FFFACD\"")) ; lemon = unknown
                          (cond ((equal h5 "+") "\"#90EE90\"") ; green = method succeeded
                                ((equal h5 "-") "\"#FFB6C1\"") ; pink  = method failed
                                (t              "\"#FFFACD\"")))))))  ; lemon = unknown
      ;; Edges
      (loop for node in all-nodes do
        (when (getf node :parent-id)
          (format out "  N~a -> N~a;~%"
                  (getf node :parent-id)
                  (getf node :node-id))))
      (format out "}~%")))   ; closes let (out ...) and with-open-file
    ;; (format t "~%Wrote ~a nodes to ~a~%" (length all-nodes) filename)
    ;; (format t "Render: dot -Tpdf ~a -o ~a.pdf~%" filename (pathname-name filename))
    filename))

;;; =========================================================================
;;; LT-specific subroutine trace hooks.
;;; These :before methods record every subroutine entry/exit in
;;; *card-cycles.ids-executed* so that proof-graph! can reconstruct the
;;; call tree.

(defmethod ipl-eval :before (start-symb)
  (push :descend *card-cycles.ids-executed*))
(defmethod ipl-descend :before (subroutine-name)
  (push :descend *card-cycles.ids-executed*))
(defmethod ipl-ascend :before (h5-status)
  (push (list :ascend h5-status) *card-cycles.ids-executed*))

;;; =========================================================================
;;; Per-proof graph generation.
;;;
;;; M001 (the LT Executive) is called once per theorem via the interpreter's
;;; flat DESCEND loop — NOT via a recursive ipl-eval call — so we cannot use
;;; a CLOS :around method to bracket it.  Instead we use trace-exprs:
;;;
;;;   "M001R000"  → start of each theorem: reset buffers, record theorem sym
;;;   "M001R220"  → positive exit of M001 (J4, proof found)  → emit graph
;;;   "M001R260"  → negative exit of M001 (J3, no proof)     → emit graph
;;;
;;; The theorem symbol is in H0/W0 at M001R000 (confirmed empirically),
;;; e.g. "*425" for *4.25.  The .dot files land in /tmp/lt-proof-425.dot.

(defvar *current-proof-sym* nil
  "Theorem symbol being proved, e.g. \"*425\".  Set at M001R000.")

(defun thm-sym->filestem (sym)
  "Convert \"*425\" → \"425\", \"*208\" → \"208\", nil → \"unknown\"."
  (if (and (stringp sym) (> (length sym) 1) (char= (aref sym 0) #\*))
      (subseq sym 1)
      (or sym "unknown")))

(defun emit-proof-graph! ()
  "Call proof-graph! for the current theorem, resetting state afterward.
   Also writes a separator + the DOT content to *lt-dotstar-stream* if bound."
  (when *current-proof-sym*
    (let* ((stem (thm-sym->filestem *current-proof-sym*))
           (pretty (m19-thm-pretty *current-proof-sym*))
           (label (format nil "Problem ~a" pretty))
           (filename (format nil "/tmp/lt-proof-~a.dot" stem)))
      ;; Separator in the dotstar so each proof is visually distinct.
      (when *lt-dotstar-stream*
        (format *lt-dotstar-stream*
                "~%// ============================================================~%// ~a~%// ============================================================~%"
                label))
      (proof-graph! filename label))
    (setf *current-proof-sym* nil)))

;;; =========================================================================
;;; LT run: create ltresults/, open timestamped log + dotstar files, run LT.
;;; All format t output is teed to the log via *standard-output* broadcast.
;;; Proof graphs are emitted to individual /tmp/lt-proof-NNN.dot files AND
;;; concatenated into the dotstar file via *lt-dotstar-stream*.

(defun lt-run-timestamp ()
  "Return a yyyymmddhhmm string for the current local time."
  (multiple-value-bind (s m h day month year)
      (decode-universal-time (get-universal-time))
    (declare (ignore s))
    (format nil "~4,'0d~2,'0d~2,'0d~2,'0d~2,'0d" year month day h m)))

(progn ;; LT
  (set-trace-mode :none)
  (setf *j15-mode* :clear-dl) ;; Documentation ambiguity, alt: :clear-dl :delete-dl
  ;(setf *!!* '(:run :jcalls) *cell-tracing-on* t) ;; :run :jcalls :jdeep :alerts :s :dr-memory :gentrace
  ;(setf *trace-cell-names-or-exprs* '("H0" "W0" "W1" "W2") *cell-tracing-on* t)
  ;; ************ NOTE P055R000 L11 HACK THAT MUST STAY IN PLACE! ************
  ;; (It's been over-riden by LTFixed code.)
  ;;(trace j8n-helper ipush)
  ;;(setf *jfn-arg-traps* '("9-2941"))
  ;;(setf *newsym-trap* '("9-2267"))
  (setf *trace-exprs*
	'(
	  ;; ----- Per-theorem proof graph capture -----

	  ;; M001R000: start of each theorem.  H0/W0 hold the theorem symbol
	  ;; (e.g. "*425").  Reset all trace buffers and record the theorem.
	  ("M001R000"
	   (progn
	     (setf *card-cycles.ids-executed* nil)
	     (clrhash *m19-annotations*)
	     (setf *m19-r000-cycle* nil)
	     (setf *current-proof-sym* (cell-symb (h0)))
	     '(format t "~%===== Proof of ~a started at cycle ~a =====~%"
		     *current-proof-sym* (h3-cycles))))

	  ;; M001R220: positive exit (J4 = H5+, proof found). Fire before J4.
	  ("M001R220" (emit-proof-graph!))

	  ;; M001R260: negative exit (J3 = H5-, no proof). Fire before J3.
	  ("M001R260" (emit-proof-graph!))

	  ;; ----- M19 annotation -----

	  ;; Capture the M19 R000 cycle so R010 can key the annotation.
	  ("M019R000"
	   (setf *m19-r000-cycle* (h3-cycles)))

	  ;; After J53 at R000 has set W0=METHOD and W1=THM, record them.
	  ("M019R010"
	   (when *m19-r000-cycle*
	     (setf (gethash *m19-r000-cycle* *m19-annotations*)
		   (list (cell-symb (cell "W1"))   ; THM  e.g. "*401"
			 (cell-symb (cell "W0")))) ; METHOD e.g. "M13"
	     (setf *m19-r000-cycle* nil)))

	  ;; Must call (trace-cell-safe-for-trace-expr) or (???) to
	  ;; trace cells otherwise messy recusion cycle ensues
	  ))

  ;; --- Create results directory and open log + dotstar files ---
  (ensure-directories-exist
   (pathname (concatenate 'string *lt-results-dir* "/")))
  (let* ((ts       (lt-run-timestamp))
         (log-path (format nil "~a/~a.log"     *lt-results-dir* ts))
         (dot-path (format nil "~a/~a.dotstar" *lt-results-dir* ts)))
    (format t "~%LT run ~a~%  log:     ~a~%  dotstar: ~a~%" ts log-path dot-path)
    (with-open-file (log-stream log-path
                                :direction :output
                                :if-exists :supersede
                                :if-does-not-exist :create)
      (with-open-file (dot-stream dot-path
                                  :direction :output
                                  :if-exists :supersede
                                  :if-does-not-exist :create)
        (let ((*standard-output*    (make-broadcast-stream *standard-output* log-stream))
              (*lt-dotstar-stream*  dot-stream))
          (load-ipl "/Users/jeffshrager/Desktop/AIHistory/IPL-V/repo/LTFixed.liplv"
                    :adv-limit 5000000))))))

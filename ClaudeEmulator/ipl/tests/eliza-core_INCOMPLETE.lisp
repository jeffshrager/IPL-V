;; ELIZA Core Pattern Matching and Response Generation

;; Pattern matching using generators
(defun find-best-rule ()
  "Find highest priority matching rule"
  (let ((max-weight 0)
        (best-rule nil))
    ;; Generate through rules
    (push-ho 'try-rule)
    (push-ho (get-cell "RULES"))
    (j100)
    ;; Return best match
    (when best-rule
      (push-ho best-rule)
      (setf *h5* '+))
    (setf *h5* '-)))

(defun try-rule ()
  "Try matching one rule (subprocess for generator)"
  (let ((rule (ipl-cell-symb *h0*)))
    ;; Get pattern and try matching
    (get-pattern rule)
    (match-pattern)
    ;; If match succeeded, compare weight
    (when (eq *h5* '+)
      (let ((weight (get-weight rule)))
        (when (> weight max-weight)
          (setf max-weight weight)
          (setf best-rule rule))))
    ;; Continue generating
    (setf *h5* '+)))

;; Variable binding management
(defun bind-variable (var)
  "Bind remaining input to variable"
  (let ((value (collect-remaining-input)))
    ;; Create binding in description list
    (push-ho value)
    (push-ho var)
    (push-ho "B1")
    (j11)))

(defun get-binding (var)
  "Get value bound to variable"
  (push-ho var)
  (push-ho "B1")
  (j10))

;; Response generation using templates
(defun generate-response ()
  "Generate response from template"
  (let ((template (get-template (ipl-cell-symb *h0*))))
    ;; Generate through template elements
    (push-ho 'generate-element)
    (push-ho template)
    (j100)))

(defun generate-element ()
  "Generate one element of response (subprocess)"
  (let ((element (ipl-cell-symb *h0*)))
    (cond
      ;; Variable - insert bound value
      ((variable-p element)
       (get-binding element)
       (j157))
      ;; Word - insert directly
      (t
       (push-ho element)
       (j157)))
    ;; Continue generating
    (setf *h5* '+)))

;; Input/Output utilities
(defun collect-remaining-input ()
  "Collect remaining input words into list"
  (j90)  ; Create new list
  (let ((list-addr (ipl-cell-symb *h0*)))
    (loop while (next-word-exists)
          do (push-ho (next-input-word))
             (push-ho list-addr)
             (j65))
    list-addr))

(defun next-word-exists ()
  "Test if more input words exist"
  (push-ho "W1")
  (j78))

(defun next-input-word ()
  "Get next word from input"
  (push-ho "W1")
  (j60)
  (ipl-cell-symb
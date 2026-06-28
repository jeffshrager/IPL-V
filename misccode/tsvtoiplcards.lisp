;;; (load (compile-file "tsvtoiplcards.lisp"))

(defparameter *col2pos*
  '(("Page")
    ("Comments" 6 40)
    ("Type" 41 41 1)
    ("Name" 43 47)
    ("Sign" 48 48)
    ("PQ" 49 50)
    ("Symb" 51 55 1)
    ("Link" 57 61 1)
    ("Comments" 63 80)))

(defun tsv2iplcards (infile outfile)
  (with-open-file (o outfile :direction :output :if-exists :supersede)
    (with-open-file (i infile)
      (read-line i nil nil) ;; Skip header
      (loop for line = (read-line i nil nil)
	    until (null line)
	    do
	    (format o "      ")
	    (loop for part in (string-split line :delimiter #\tab)
		  as (type start end skip) in *col2pos*
		  when start ;; This skips page which isn't part of IPL
		  do
		  (format o "~vA" (1+ (- end start)) part)
		  (when skip (format o "~vA" skip ""))
		  finally (format o "~%"))))))
		   
(defun string-split (string &key (delimiter #\space) (convert-num-values? nil))
  "Split string into substrings delimited by delimiter"
  (let ((substrings '())
        (length (length string))
        (last 0))
    (flet ((add-substring 
	    (i)
	    (push (subseq string last i)
		  substrings)))
	  (dotimes (i length)
	    (when (eq (char string i) delimiter)
	      (add-substring i)
	      (setq last (1+ i))))
	  (add-substring length)
	  (let ((substrings (nreverse substrings)))
	    (if convert-num-values?
		(loop for string in substrings
		      as v = (ignore-errors (read-from-string string))
		      if (numberp v)
		      collect v
		      else 
		      collect string)
	      substrings)))))

(tsv2iplcards "Ackermann.tsv" "Ackermann.iplcards")

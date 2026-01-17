(load "iplv_lib.lisp")

(defun test-j74 ()
  (format t "~%--- Testing J74 ---~%")
  
  ;; Initialize machine (needed for H etc.)
  (initialize-machine)
  
  ;; Create a simple list L1: A -> B -> 0
  ;; We define cells manually using make-cell!
  (let* ((cell-b (make-cell! :name "9-2" :symb "B" :link "0"))
         (cell-a (make-cell! :name "9-1" :symb "A" :link "9-2"))
         (head-l1 (make-cell! :name "L1" :symb "0" :link "9-1")))
         
    (format t "Original L1:~%")
    (pl "L1")
    
    ;; Push L1 name to H0 for J74
    (ipush "H0" "L1")
    
    (format t "~%Calling J74 on L1...~%")
    (J74)
    
    ;; Result is in H0
    (let ((result-name (cell-symb (cell "H0"))))
      (format t "~%Resulting List Name: ~s~%" result-name)
      (format t "Resulting List Structure:~%")
      (pl result-name)
      
      (format t "~%Checking Original L1 (should be unchanged):~%")
      (pl "L1")
      
      (let ((l1-link (cell-link (cell "L1"))))
         (if (string-equal l1-link "9-1")
             (format t "~%L1 Link verified as 9-1 (OK)~%")
             (format t "~%L1 Link CHANGED to ~s (FAIL - Original Modified)~%"))
         
         (let ((cell-9-1 (cell "9-1")))
            (if (equal cell-9-1 (gethash "9-1" *symtab*))
                (format t "Cell 9-1 is still the same object? ~s~%" cell-9-1)
                (format t "Cell 9-1 object changed?~%"))
         )
      )
      
      ;; Verify it is a COPY (different cells)
      (if (string-equal result-name "L1")
          (format t "~%FAIL: Result Name is same as Input Name (L1).~%")
          (progn
             (format t "~%Result Name is different (OK). Check structure...~%")
             ;; Check if cells in result are different from original
             (let ((res-link (cell-link (cell result-name))))
                (if (string-equal res-link "9-1")
                    (format t "FAIL: Result list points to '9-1' (Original Cell Name). Should be new name.~%")
                    (format t "SUCCESS: Result list points to '~s' (New Cell Name).~%" res-link)))
          ))
    )
  )
)

(test-j74)
(sb-ext:exit)

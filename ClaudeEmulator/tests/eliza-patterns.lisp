;; ELIZA Pattern and Response Data

;; Pattern definitions for common inputs
(defvar *pattern-data*
  '(;; "I am <X>" pattern
    ("P10"  0 0 "W1" "9-1")     ; I
    ("9-1"  0 0 "W2" "9-2")     ; AM
    ("9-2"  0 0 "V1" 0)         ; Variable binding
    
    ;; "I <X> you" pattern
    ("P20"  0 0 "W1" "9-10")    ; I
    ("9-10" 0 0 "V1" "9-11")    ; Verb binding
    ("9-11" 0 0 "W3" 0)         ; YOU
    
    ;; "I feel <X>" pattern
    ("P30"  0 0 "W1" "9-20")    ; I
    ("9-20" 0 0 "W4" "9-21")    ; FEEL
    ("9-21" 0 0 "V1" 0)         ; Feeling binding

    ;; "Why <X>" pattern
    ("P40"  0 0 "W5" "9-30")    ; WHY
    ("9-30" 0 0 "V1" 0)))       ; Rest of question

;; Response templates
(defvar *response-data*
  '(;; General responses
    ("T10"  0 0 "R1" "9-40")    ; "Tell me more about <X>"
    ("9-40" 0 0 "R2" "9-41")    ; "Why do you think <X>?"
    ("9-41" 0 0 "R3" 0)         ; "How does <X> make you feel?"
    
    ;; Specific response components
    ("R1"   0 0 "WT1" "9-50")   ; "Tell"
    ("9-50" 0 0 "WT2" "9-51")   ; "me"
    ("9-51" 0 0 "WT3" "9-52")   ; "more"
    ("9-52" 0 0 "WT4" "9-53")   ; "about"
    ("9-53" 0 0 "V1" 0)         ; Insert variable binding

    ;; Memory structure for previous responses
    ("M1"   0 0 "H1" "9-60")    ; History list head
    ("9-60" 0 0 "P1" "9-61")    ; Pattern used
    ("9-61" 0 0 "R1" 0)))       ; Response used

;; Word dictionary
(defvar *dictionary-data*
  '(;; Common words as BCD data terms
    ("WT1"  0 1 "TELL" 0)
    ("WT2"  0 1 "ME" 0)
    ("WT3"  0 1 "MORE" 0)
    ("WT4"  0 1 "ABOUT" 0)
    ("WT5"  0 1 "WHY" 0)
    ("WT6"  0 1 "DO" 0)
    ("WT7"  0 1 "YOU" 0)
    ("WT8"  0 1 "THINK" 0)
    ("WT9"  0 1 "FEEL" 0)
    ("WT10" 0 1 "?" 0)))

;; Pattern weights for prioritizing responses
(defvar *weight-data*
  '(;; NAME P Q SYMB LINK
    ("N1"   0 1 1 0)    ; Weight = 1
    ("N2"   0 1 2 0)    ; Weight = 2
    ("N3"   0 1 3 0)    ; Weight = 3
    ("N4"   0 1 4 0)    ; Weight = 4
    ("N5"   0 1 5 0)))  ; Weight = 5

;; Binding management
(defvar *binding-data*
  '(;; Description list for variable bindings
    ("B1"   9-1 0 0)           ; Bindings list head
    ("9-1"  0 0 "V1" "9-70")   ; Variable name
    ("9-70" 0 0 "VB1" 0)))     ; Bound value

(set-logic QF_BV)  

; The main assertion - we're asking Z3 to find a model where this is TRUE
; If Z3 says "unsat", then no such model exists (programs are equivalent)
; If Z3 says "sat", then it found a counterexample

(assert 
  (not 
    (and 
      true  ; SmtBoolAnd SmtTrue
      (= 
        ; First expression result
        (ite 
          (= #x00000000 #x00000000)  ; if 0 == 0
          (bvadd #x00000001 #x00000000)  ; then 1 + 0 
          #x00000000                      ; else 0
        )
        ; Second expression result  
        (ite 
          (= #x00000000 #x00000000)  ; if 0 == 0
          (bvadd #x00000001 #x00000000)  ; then 1 + 0
          #x00000000                      ; else 0  
        )
      )
    )
  )
)

(check-sat)
(exit)
(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|f$unknown:2| E D)
        (and (not (= 0 C)) (= D (- 2)) (= A E) (= (= 0 C) (<= (- 1) B)))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (and (= (= 0 C) (<= (- 1) B))
     (not (= 0 D))
     (= 0 C)
     (= A (+ (- 1) E))
     (= E (* 2 B))
     (not (= (= 0 D) (<= B 1))))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (not (= (= 0 D) (<= B 1)))
     (= 0 C)
     (= 0 D)
     (= A B)
     (= (= 0 C) (<= (- 1) B)))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (|f$unknown:2| E A)
        (|f$unknown:2| C B)
        (and (not (= (= 0 F) (>= E 0)))
     (not (= 0 D))
     (= 0 F)
     (= B 0)
     (not (= (= 0 D) (>= A 2))))
      )
      false
    )
  )
)

(check-sat)
(exit)

(set-logic HORN)


(declare-fun |f$unknown:2| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (|f$unknown:2| H G)
        (and (= (= 0 D) (<= 2 B))
     (= (= 0 C) (<= (- 2) B))
     (not (= 0 E))
     (= 0 D)
     (= 0 C)
     (= G (+ (- 1) F))
     (= F (* 2 B))
     (= A H)
     (not (= (= 0 E) (<= B 2))))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|f$unknown:2| E D)
        (and (not (= 0 C)) (= D (- 3)) (= A E) (= (= 0 C) (<= (- 2) B)))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (and (= (= 0 C) (<= (- 2) B))
     (not (= 0 D))
     (= 0 C)
     (= A (+ (- 1) E))
     (= E (* 2 B))
     (= (= 0 D) (<= 2 B)))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (and (= (= 0 C) (<= (- 2) B))
     (not (= (= 0 E) (<= B 2)))
     (= 0 D)
     (= 0 C)
     (= 0 E)
     (= A B)
     (= (= 0 D) (<= 2 B)))
      )
      (|f$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|f$unknown:2| B A)
        (and (= 0 C) (= A 3) (not (= (= 0 C) (>= B 0))))
      )
      false
    )
  )
)

(check-sat)
(exit)

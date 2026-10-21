(set-logic HORN)


(declare-fun |f$unknown:4| ( Int Int ) Bool)
(declare-fun |decr$unknown:2| ( Int Int ) Bool)
(declare-fun |f$unknown:6| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (= A (+ (- 1) B))
      )
      (|decr$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|decr$unknown:2| A D)
        (and (not (= 0 C)) (not (= (= 0 C) (>= B 3))))
      )
      (|f$unknown:4| A D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|f$unknown:4| D B)
        (and (not (= 0 C)) (= A D) (= (= 0 C) (<= B 0)))
      )
      (|f$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= 0 C) (= A 1) (= (= 0 C) (<= B 0)))
      )
      (|f$unknown:6| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|f$unknown:6| C A)
        (and (= (= 0 D) (<= C 0)) (not (= 0 B)) (= 0 D) (not (= (= 0 B) (>= A 3))))
      )
      false
    )
  )
)

(check-sat)
(exit)

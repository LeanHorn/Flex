(set-logic HORN)


(declare-fun |repeat$unknown:2| ( Int Int ) Bool)
(declare-fun |succ$unknown:7| ( Int Int ) Bool)
(declare-fun |repeat$unknown:5| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (|repeat$unknown:2| A B)
        (and (= 0 D) (= E (+ (- 1) C)) (not (= (= 0 D) (= C 0))))
      )
      (|repeat$unknown:2| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (|succ$unknown:7| A C)
        (= B 0)
      )
      (|repeat$unknown:2| A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) 
    (=>
      (and
        (|repeat$unknown:2| G F)
        (|repeat$unknown:5| F C E)
        (and (= 0 D) (= A G) (= E (+ (- 1) B)) (not (= (= 0 D) (= B 0))))
      )
      (|repeat$unknown:5| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (not (= 0 D)) (= A C) (not (= (= 0 D) (= B 0))))
      )
      (|repeat$unknown:5| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (= A (+ 1 B))
      )
      (|succ$unknown:7| A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|repeat$unknown:5| C B A)
        (and (= 0 D) (= B 0) (not (= (= 0 D) (>= C A))))
      )
      false
    )
  )
)

(check-sat)
(exit)

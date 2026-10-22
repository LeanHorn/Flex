(set-logic HORN)


(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |loop$unknown:3| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (|loop$unknown:3| F E B)
        (and (= (= 0 D) (<= 0 C))
     (= (= 0 H) (<= B 2))
     (= 0 G)
     (= 0 D)
     (not (= 0 H))
     (= E (+ (- 1) C))
     (= A F)
     (= (= 0 G) (<= 1 B)))
      )
      (|loop$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (|loop$unknown:3| G F E)
        (and (= (= 0 H) (<= 1 B))
     (= 0 D)
     (not (= 0 H))
     (= F (+ (- 1) C))
     (= E (+ (- 1) B))
     (= A G)
     (= (= 0 D) (<= 0 C)))
      )
      (|loop$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (|loop$unknown:3| I H G)
        (and (= (= 0 E) (<= 1 B))
     (= (= 0 D) (<= 0 C))
     (= 0 F)
     (= 0 E)
     (= 0 D)
     (= A I)
     (= H (+ (- 1) C))
     (= G (+ 3 (* (- 1) B)))
     (= (= 0 F) (<= B 2)))
      )
      (|loop$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (not (= 0 D)) (= A B) (= (= 0 D) (<= 0 C)))
      )
      (|loop$unknown:3| A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (|loop$unknown:3| G A F)
        (|loop$unknown:3| D A C)
        (and (not (= (= 0 H) (>= G 3)))
     (= 0 E)
     (not (= 0 H))
     (= F 3)
     (= C 1)
     (= B 1)
     (not (= (= 0 E) (>= D 0))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (|loop$unknown:3| C A B)
        (and (= 0 D) (= B 3) (not (= (= 0 D) (>= C 3))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)

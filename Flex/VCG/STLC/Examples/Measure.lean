import Flex.VCG.STLC.Examples.Ord

open STLC

/-! # Measures

  A measure is a structurally recursive function on a datatype, declared with
  one body per constructor (sprite §7.1.3): `len Nil = 0`,
  `len (Cons h t) = 1 + len t`. In refinements it is an uninterpreted function
  of a variable (`Term.mbvar`/`Term.mfvar`): verification conditions only know
  the equations recorded where a value is built (`Cons(h, t) : list{len ν = 1 + len t}`)
  and where it is matched (in `case xs of Cons p ⇒ …`, the payload
  `p = (h, (t, u))` ends in a unit `u : Int{len xs = 1 + len t}`). -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var DataDecl.measBody? Base.constSubst
  TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons caseL

/-! ## Lists with a length measure -/

/-- `measure len : list α → Int`, `len Nil = 0`, `len (Cons h t) = 1 + len t`. -/
def lenListDecl : DataDecl :=
  { listDecl with measures := [("len", [.const 0, .add (.const 1) (.meas "len" 1)])] }
def lenEnv : DEnv := [("list", lenListDecl)]

theorem lenEnv_wf : lenEnv.wfB = true := by decide

/-- `len` of the variable at de Bruijn index `i`. -/
abbrev lenB (i : Nat) : Term .int := .mbvar "len" i

/-- `list τ` whose length is `t` (ν = `BVar 0`). -/
abbrev ListLen (τ : Ty) (t : Term .int) : Ty := .dataL "list" [τ] (.fmla (.eq .int (lenB 0) t))

/-! ## `length : ∀α. xs:list α → Int{ν = len xs}` -/

abbrev lengthTy : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.refine .int (.fmla (.eq .int (.bvar .int 0) (lenB 1)))))

/-- `Λα. fix go. λxs. case xs of Nil _ => 0
                  | Cons p => let (h, (t, _)) = p; let r = go t; 1 + r` -/
abbrev lengthE : Exp :=
  .tabs .star (.fix (caseL (.bvar 0)                      -- xs=0 go=1
    [ .iconst 0
    , .split (.bvar 0) (.split (.bvar 0)                  -- u=0 t=1 q=2 h=3 p=4 xs=5 go=6
        (.letin (.app (.bvar 6) (.bvar 1))                -- r = go t
        (.letin (.iconst 1)                               -- one   (r=1 …)
        (.add (.bvar 0) (.bvar 1))))) ]))

/-- The verification condition is the two equations a `case` on `xs` reveals,
    with `len` uninterpreted:
    `len xs = 0 → 0 = len xs` and `len xs = 1 + len t → 1 + len t = len xs`. -/
theorem meas_length : ∃ κ : KEnv, Check lenEnv κ [] lengthE lengthTy := by
  simp only [lengthE, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-! ## `append : ∀α. xs:list α → ys:list α → list α{len ν = len xs + len ys}` -/

abbrev appendLenTy : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.arrow (ListT (Par 0))
    (ListLen (Par 0) (.add (lenB 2) (lenB 1)))))

/-- The same program as `appendE` (DataExamples), at the precise type: the
    recursive call `go t ys` returns `len t + len ys` elements, and
    `Cons(h, r)` has one more. -/
theorem meas_append : ∃ κ : KEnv, Check lenEnv κ [] appendE appendLenTy := by
  simp only [appendE, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-! ## `head : ∀α. xs:list α{0 < len ν} → α` — the `Nil` case is unreachable -/

abbrev headTy : Ty :=
  .forall .star (.arrow (.dataL "list" [Par 0] (.fmla (.not (.leqI (lenB 0) (.const .int 0)))))
    (Par 0))

/-- `Λα. λxs. case xs of Nil _ => unreachable | Cons p => let (h, _) = p; h` -/
abbrev headE : Exp :=
  .tabs .star (.lam (caseL (.bvar 0) [.unreach, .split (.bvar 0) (.bvar 1)]))

theorem meas_head : ∃ κ : KEnv, Check lenEnv κ [] headE headTy := by
  simp only [headE, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-- Without the precondition, `head` is rejected: nothing rules out `Nil`. -/
theorem meas_head_bad (κ : KEnv) :
    ¬ topVC κ [] headE (.forall .star (.arrow (ListT (Par 0)) (Par 0))) lenEnv := by
  simp [topVC, headE, lenEnv, lenListDecl, listDecl]
  exact ⟨{ map := fun _ => .iconst 0 }, rfl⟩

/-! ## `map` preserves the length -/

abbrev mapLenTy : Ty := .forall .star (.forall .star
  (.arrow (.arrow (Par 1) (Par 0)) (.arrow (ListT (Par 1)) (ListLen (Par 0) (lenB 1)))))

theorem meas_map : ∃ κ : KEnv, Check lenEnv κ [] mapE mapLenTy := by
  simp only [mapE, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-! ## Building a list: `[1, 2]` has length 2 (and not 3) -/

/-- `let one = 1; let two = 2; let nil = Nil[Int]; let l = Cons(two, nil); Cons(one, l)` -/
abbrev twoE : Exp :=
  .letin (.iconst 1) (.letin (.iconst 2)              -- two=0 one=1
  (.letin (nilE TT)                                   -- nil
  (.letin (consE TT (.bvar 1) (.bvar 0))              -- l = Cons(two, nil)
  (consE TT (.bvar 3) (.bvar 0)))))                   -- Cons(one, l)

theorem meas_two : ∃ κ : KEnv, Check lenEnv κ [] twoE (ListLen TT (.const .int 2)) := by
  simp only [twoE, lenEnv, lenListDecl, listDecl]
  generate
  solve

theorem meas_two_bad (κ : KEnv) : ¬ topVC κ [] twoE (ListLen TT (.const .int 3)) lenEnv := by
  simp [topVC, twoE, lenEnv, lenListDecl, listDecl]
  -- a model of the recorded equations in which `[1, 2]` has length 2
  refine ⟨{ map := fun y => .iconst y.length,
            sorts := { meas := fun _ v => match v with | .iconst n => n - 3 | _ => 0 } }, ?_⟩
  decide

/-! ## Inference over a measure: `κ(len ν)`

  `l = Cons(1, Nil)` is annotated with an unknown refinement of its length,
  `list Int{κ(len ν)}`, and passed to `head`, which needs `0 < len l`. The solver
  infers `κ(n) := 1 ≤ n`. -/

theorem meas_infer : ∃ κ : KEnv, Check lenEnv κ []
    (.letin (.iconst 1)                                                 -- one
    (.letin (nilE TT)                                                   -- nil
    (.letin (.ann (consE TT (.bvar 1) (.bvar 0))
              (.dataL "list" [TT] (.kapp "k" [⟨.int, lenB 0⟩])))         -- l : list Int{k(len ν)}
    (.app (.tapp (.ann headE headTy) TT) (.bvar 0)))))                  -- head[Int] l
    TT := by
  simp only [headE, headTy, lenEnv, lenListDecl, listDecl]
  generate
  zap
  grind

/-! ## End to end: `head [1, 2]` never reaches its `unreachable` branch -/

/-- `let one = 1; let two = 2; let nil = Nil; let l = Cons(two, nil); head[Int] (Cons(one, l))` -/
abbrev headClientE : Exp :=
  .letin (.iconst 1) (.letin (.iconst 2)              -- two=0 one=1
  (.letin (nilE TT)                                   -- nil
  (.letin (consE TT (.bvar 1) (.bvar 0))              -- l = Cons(two, nil)
  (.letin (consE TT (.bvar 3) (.bvar 0))              -- l' = Cons(one, l)
  (.app (.tapp (.ann headE headTy) TT) (.bvar 0))))))  -- head[Int] l'

theorem meas_headClient_vc : ∃ κ : KEnv, Check lenEnv κ [] headClientE TT := by
  simp only [headClientE, headE, headTy, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-- Running the client never gets stuck — in particular `head` never takes its
    `Nil` branch, which `len` rules out — and any value it returns is an
    integer. -/
theorem meas_headClient_safe (n : Nat) :
    ∃ o, Run n headClientE o ∧ ∀ v m, o = .val v m → ∃ i : Int, v = .iconst i := by
  obtain ⟨κ, hc⟩ := meas_headClient_vc
  have hh := check_to_hastype TEnv.WFBVars.empty
    (by simp [Exp.WFBVars, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar,
              Term.hasBVar])
    (by simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar]) hc
  obtain ⟨o, hrun, hres⟩ := type_safety lenEnv_wf hh n
  refine ⟨o, hrun, fun v m ho => ?_⟩
  have := hres v m ho
  simp only [TyDenote, BaseDen] at this
  obtain ⟨⟨i, rfl⟩, _⟩ := this
  exact ⟨i, rfl⟩

/-! ## Lemmas as programs: `len ≥ 0`

  With `len` uninterpreted, `0 ≤ len xs` takes induction, i.e. recursion: the
  program `nonneg` checks against `xs:list α → Int{0 ≤ len xs}`. A client calls
  it where it needs the fact (`let _ = nonneg t`). This is sound under partial
  correctness without proving that `nonneg` terminates, because the call is
  executed; assuming the statement without the call would need termination. -/

/-- `nonneg : ∀α. xs:list α → Int{0 ≤ len xs}` -/
abbrev nonnegTy : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.refine .int (.fmla (.leqI (.const .int 0) (lenB 1)))))

/-- `Λα. fix go. λxs. case xs of Nil _ => 0 | Cons p => let (h, (t, _)) = p; go t` -/
abbrev nonnegE : Exp :=
  .tabs .star (.fix (caseL (.bvar 0)                      -- xs=0 go=1
    [ .iconst 0
    , .split (.bvar 0) (.split (.bvar 0)                  -- u=0 t=1 q=2 h=3 p=4 xs=5 go=6
        (.app (.bvar 6) (.bvar 1))) ]))                   -- go t

/-- The lemma's verification condition is the induction. -/
theorem meas_nonneg : ∃ κ : KEnv, Check lenEnv κ [] nonnegE nonnegTy := by
  simp only [nonnegE, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-- `cons : ∀α. α → t:list α → list α{0 < len ν}` -/
abbrev consPosTy : Ty :=
  .forall .star (.arrow (Par 0) (.arrow (ListT (Par 0))
    (.dataL "list" [Par 0] (.fmla (.not (.leqI (lenB 0) (.const .int 0)))))))

/-- `Λα. λh. λt. Cons(h, t)` -/
abbrev consPosE : Exp := .tabs .star (.lam (.lam (consE (Par 0) (.bvar 1) (.bvar 0))))

/-- `Λα. λh. λt. let _ = nonneg[α] t; Cons(h, t)` -/
abbrev consPosLemmaE : Exp :=
  .tabs .star (.lam (.lam                                               -- t=0 h=1
    (.letin (.app (.tapp (.ann nonnegE nonnegTy) (Par 0)) (.bvar 0))    -- _ = nonneg[α] t
      (consE (Par 0) (.bvar 2) (.bvar 1)))))                            -- Cons(h, t)

/-- With the lemma: `len ν = 1 + len t` and `0 ≤ len t` give `0 < len ν`. -/
theorem meas_consPos : ∃ κ : KEnv, Check lenEnv κ [] consPosLemmaE consPosTy := by
  simp only [consPosLemmaE, nonnegE, nonnegTy, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-- Without the lemma, `t` might have negative length. -/
theorem meas_consPos_bad (κ : KEnv) : ¬ topVC κ [] consPosE consPosTy lenEnv := by
  simp [topVC, consPosE, consPosTy, lenEnv, lenListDecl, listDecl]
  -- `t` of length -1 makes `Cons(h, t)` have length 0
  refine ⟨{ map := fun y => .iconst y.length,
            sorts := { meas := fun _ v => match v with | .iconst n => n - 3 | _ => 0 } }, ?_⟩
  decide

/-! ## Reading `Int` fields: `sum` of an integer list -/

/-- `ilist = INil | ICons (Int, ilist)` with `sum INil = 0`, `sum (ICons h t) = h + sum t`. -/
def ilistDecl : DataDecl :=
  { params := [], ctorFields := [("INil", []), ("ICons", [TT, .dataL "ilist" []])],
    measures := [("sum", [.const 0, .add (.field 0) (.meas "sum" 1)])] }
def ilistEnv : DEnv := [("ilist", ilistDecl)]

theorem ilistEnv_wf : ilistEnv.wfB = true := by decide

/-- Reading a field as an `Int` requires it to be declared `Int`: summing the
    elements of a polymorphic `list α` (field `0 : α`) is rejected. -/
theorem sumPoly_wf_bad :
    DEnv.wfB [("list", { listDecl with
      measures := [("sum", [.const 0, .add (.field 0) (.meas "sum" 1)])] })] = false := by
  decide

/-- … and branching on a field requires it to be declared `Bool`. -/
theorem iteBOnInt_wf_bad :
    DEnv.wfB [("ilist", { ilistDecl with
      measures := [("sum", [.const 0, .iteB 0 (.const 1) (.const 0)])] })] = false := by
  decide

/-- `sumList : xs:ilist → Int{ν = sum xs}`:
    `fix go. λxs. case xs of INil _ => 0 | ICons p => let (h, (t, _)) = p; let r = go t; h + r` -/
abbrev sumIListTy : Ty :=
  .arrow (.dataL "ilist" []) (.refine .int (.fmla (.eq .int (.bvar .int 0) (.mbvar "sum" 1))))
abbrev sumIListE : Exp :=
  .fix (caseL (.bvar 0)                                   -- xs=0 go=1
    [ .iconst 0
    , .split (.bvar 0) (.split (.bvar 0)                  -- u=0 t=1 q=2 h=3 p=4 xs=5 go=6
        (.letin (.app (.bvar 6) (.bvar 1))                -- r = go t
        (.add (.bvar 4) (.bvar 0)))) ])                   -- h + r

/-- The match records `sum xs = h + sum t`, reading the field `h`. -/
theorem meas_sumIList : ∃ κ : KEnv, Check ilistEnv κ [] sumIListE sumIListTy := by
  simp only [sumIListE, ilistEnv, ilistDecl]
  generate
  solve

/-! ## Trees: `size` -/

/-- `tree α = Leaf | Node (tree α, α, tree α)`, `size Leaf = 0`,
    `size (Node l x r) = 1 + size l + size r`. -/
def treeDecl : DataDecl :=
  { params := [.star],
    ctorFields := [("Leaf", []), ("Node", [.dataL "tree" [Par 0], Par 0, .dataL "tree" [Par 0]])],
    variances := [.co],
    measures := [("size", [.const 0, .add (.const 1) (.add (.meas "size" 0) (.meas "size" 2))])] }
def treeEnv : DEnv := [("tree", treeDecl)]

theorem treeEnv_wf : treeEnv.wfB = true := by decide

abbrev TreeT (τ : Ty) (r : Refinement := ttR) : Ty := .dataL "tree" [τ] r
abbrev sizeB (i : Nat) : Term .int := .mbvar "size" i

/-- `mirror : ∀α. t:tree α → tree α{size ν = size t}` -/
abbrev mirrorTy : Ty :=
  .forall .star (.arrow (TreeT (Par 0)) (TreeT (Par 0) (.fmla (.eq .int (sizeB 0) (sizeB 1)))))

/-- `Λα. fix go. λt. case t of
      Leaf _ => Leaf
      Node p => let (l, (x, (r, _))) = p; let l' = go l; let r' = go r; Node(r', x, l')` -/
abbrev mirrorE : Exp :=
  .tabs .star (.fix (caseL (.bvar 0)                                  -- t=0 go=1
    [ .ctor "tree" 0 [Par 0] unitE
    , .split (.bvar 0) (.split (.bvar 0) (.split (.bvar 0)            -- u=0 r=1 q'=2 x=3 q=4 l=5 p=6 t=7 go=8
          (.letin (.app (.bvar 8) (.bvar 5))                          -- l' = go l
          (.letin (.app (.bvar 9) (.bvar 2))                          -- r' = go r  (l'=0 u=1 r=2)
          (.ctor "tree" 1 [Par 0] (.pair (.bvar 0) (.pair (.bvar 5) (.pair (.bvar 1) unitE)))))))) ]))

theorem meas_mirror : ∃ κ : KEnv, Check treeEnv κ [] mirrorE mirrorTy := by
  simp only [mirrorE, treeEnv, treeDecl]
  generate
  solve

/-- The lemma `sizeNonneg : ∀α. t:tree α → Int{0 ≤ size t}`: the recursion
    makes one call per subtree (two induction hypotheses).
    `Λα. fix go. λt. case t of Leaf _ => 0
                     | Node p => let (l, (x, (r, _))) = p; let a = go l; go r` -/
abbrev sizeNonnegTy : Ty :=
  .forall .star (.arrow (TreeT (Par 0)) (.refine .int (.fmla (.leqI (.const .int 0) (sizeB 1)))))
abbrev sizeNonnegE : Exp :=
  .tabs .star (.fix (caseL (.bvar 0)                                  -- t=0 go=1
    [ .iconst 0
    , .split (.bvar 0) (.split (.bvar 0) (.split (.bvar 0)            -- u=0 r=1 q'=2 x=3 q=4 l=5 p=6 t=7 go=8
          (.letin (.app (.bvar 8) (.bvar 5))                          -- a = go l
          (.app (.bvar 9) (.bvar 2))))) ]))                           -- go r   (a=0 u=1 r=2)

theorem meas_sizeNonneg : ∃ κ : KEnv, Check treeEnv κ [] sizeNonnegE sizeNonnegTy := by
  simp only [sizeNonnegE, treeEnv, treeDecl]
  generate
  solve

/-- `node : ∀α. l:tree α → x:α → r:tree α → tree α{size l < size ν}` needs
    `size r ≥ 0`, which the lemma provides:
    `Λα. λl. λx. λr. let _ = sizeNonneg[α] r; Node(l, x, r)` -/
abbrev nodeTy : Ty :=
  .forall .star (.arrow (TreeT (Par 0)) (.arrow (Par 0) (.arrow (TreeT (Par 0))
    (TreeT (Par 0) (.fmla (.not (.leqI (sizeB 0) (sizeB 3))))))))
abbrev nodeE : Exp :=
  .tabs .star (.lam (.lam (.lam                                               -- r=0 x=1 l=2
    (.letin (.app (.tapp (.ann sizeNonnegE sizeNonnegTy) (Par 0)) (.bvar 0))  -- _ = sizeNonneg[α] r
      (.ctor "tree" 1 [Par 0] (.pair (.bvar 3) (.pair (.bvar 2) (.pair (.bvar 1) unitE))))))))

theorem meas_node : ∃ κ : KEnv, Check treeEnv κ [] nodeE nodeTy := by
  simp only [nodeE, sizeNonnegE, sizeNonnegTy, treeEnv, treeDecl]
  generate
  solve

/-! ## `filterGe` shrinks: `len ν ≤ len xs`

  The path-sensitive filter of DataExamples, at a type that also bounds the
  result's length; the element refinement of the `Cons` instance is still
  inferred. -/

abbrev filterGeLenTy : Ty :=
  .arrow TT (.arrow (ListT TT)
    (.dataL "list" [.refine .int (.fmla (.leqI (.bvar .int 2) (.bvar .int 0)))]
      (.fmla (.leqI (lenB 0) (lenB 1)))))

theorem meas_filterGe : ∃ κ : KEnv, Check lenEnv κ [] filterGeE filterGeLenTy := by
  simp only [filterGeE, lenEnv, lenListDecl, listDecl]
  generate
  zap
  grind

/-! ## `insert` into an ordered list adds one element

  The ordered-list `insert` of OrdExamples (polymorphic recursion included), at
  `∀α:B. x:α → ys:olist α → olist α{len ν = 1 + len ys}`. -/

def olistLenEnv : DEnv :=
  [("olist", { olistDecl with measures := [("len", [.const 0, .add (.const 1) (.meas "len" 1)])] })]

theorem olistLenEnv_wf : olistLenEnv.wfB = true := by decide

abbrev insLenTy : Ty := .forall .B (.arrow (Par 0) (.arrow (OListT (Par 0))
  (.dataL "olist" [Par 0] (.fmla (.eq .int (lenB 0) (.add (.const .int 1) (lenB 1)))))))

theorem meas_insert : ∃ κ : KEnv, Check olistLenEnv κ [] insE insLenTy := by
  simp only [insE, olistLenEnv, olistDecl]
  generate
  solve

/-! ## Conditionals: tree `height`

  `height (Node l x r) = 1 + max (height l) (height r)` uses a conditional
  (`MBody.max a b = if a ≤ b then b else a`), which becomes an `ite` term in
  the logic. -/

/-- Trees with both `size` and `height`. -/
def htreeDecl : DataDecl :=
  { treeDecl with
    measures := treeDecl.measures ++
      [("height", [.const 0, .add (.const 1) (.max (.meas "height" 0) (.meas "height" 2))])] }
def htreeEnv : DEnv := [("tree", htreeDecl)]

theorem htreeEnv_wf : htreeEnv.wfB = true := by decide

abbrev heightB (i : Nat) : Term .int := .mbvar "height" i

/-- `mirror` preserves the height too (the `max` swaps its arguments). -/
abbrev mirrorHTy : Ty :=
  .forall .star (.arrow (TreeT (Par 0))
    (TreeT (Par 0) (.fmla (.and (.eq .int (sizeB 0) (sizeB 1)) (.eq .int (heightB 0) (heightB 1))))))

theorem meas_mirrorHeight : ∃ κ : KEnv, Check htreeEnv κ [] mirrorE mirrorHTy := by
  simp only [mirrorE, htreeEnv, htreeDecl, treeDecl]
  generate
  solve

/-- A lemma relating two measures, `0 ≤ height t ≤ size t`, by recursion on
    both subtrees:
    `Λα. fix go. λt. case t of Leaf _ => 0
                     | Node p => let (l, (x, (r, _))) = p; let a = go l; go r` -/
abbrev heightLeSizeTy : Ty :=
  .forall .star (.arrow (TreeT (Par 0))
    (.refine .int (.fmla (.and (.leqI (.const .int 0) (heightB 1)) (.leqI (heightB 1) (sizeB 1))))))

theorem meas_heightLeSize : ∃ κ : KEnv, Check htreeEnv κ [] sizeNonnegE heightLeSizeTy := by
  simp only [sizeNonnegE, htreeEnv, htreeDecl, treeDecl]
  generate
  solve

/-! ## Reading `Bool` fields: `countTrue`

  `iteB i t e` branches on the `Bool` field `i` (`and`/`or`/`not` of fields by
  nesting); it becomes an `ite` on that field in the logic. -/

/-- `blist = BNil | BCons (Bool, blist)` with `countTrue BNil = 0`,
    `countTrue (BCons b t) = (if b then 1 else 0) + countTrue t`. -/
def blistDecl : DataDecl :=
  { params := [], ctorFields := [("BNil", []), ("BCons", [.refine .bool ttR, .dataL "blist" []])],
    measures := [("countTrue",
      [.const 0, .iteB 0 (.add (.const 1) (.meas "countTrue" 1)) (.meas "countTrue" 1)])] }
def blistEnv : DEnv := [("blist", blistDecl)]

theorem blistEnv_wf : blistEnv.wfB = true := by decide

abbrev countB (i : Nat) : Term .int := .mbvar "countTrue" i

/-- `count : xs:blist → Int{ν = countTrue xs}`:
    `fix go. λxs. case xs of BNil _ => 0
                  | BCons p => let (b, (t, _)) = p; let r = go t; if b then 1 + r else r` -/
abbrev countTy : Ty :=
  .arrow (.dataL "blist" []) (.refine .int (.fmla (.eq .int (.bvar .int 0) (countB 1))))
abbrev countE : Exp :=
  .fix (caseL (.bvar 0)                                   -- xs=0 go=1
    [ .iconst 0
    , .split (.bvar 0) (.split (.bvar 0)                  -- u=0 t=1 q=2 b=3 p=4 xs=5 go=6
        (.letin (.app (.bvar 6) (.bvar 1))                -- r = go t     (r=0 u=1 t=2 q=3 b=4)
        (.ite (.bvar 4)
          (.letin (.iconst 1) (.add (.bvar 0) (.bvar 1))) -- 1 + r
          (.bvar 0)))) ])                                 -- r

/-- The match records `countTrue xs = (if b then 1 + countTrue t else countTrue t)`;
    the branch on `b` picks the matching side. -/
theorem meas_count : ∃ κ : KEnv, Check blistEnv κ [] countE countTy := by
  simp only [countE, blistEnv, blistDecl]
  generate
  solve

/-- `let tt = true; let ff = false; let n = BNil; let l = BCons(ff, n); BCons(tt, l)`
    has exactly one `true`. -/
abbrev oneTrueE : Exp :=
  .letin (.bconst true) (.letin (.bconst false)           -- ff=0 tt=1
  (.letin (.ctor "blist" 0 [] unitE)                      -- n
  (.letin (.ctor "blist" 1 [] (.pair (.bvar 1) (.pair (.bvar 0) unitE)))  -- l = BCons(ff, n)
  (.ctor "blist" 1 [] (.pair (.bvar 3) (.pair (.bvar 0) unitE))))))       -- BCons(tt, l)

theorem meas_oneTrue : ∃ κ : KEnv, Check blistEnv κ [] oneTrueE (.dataL "blist" [] (.fmla (.eq .int (countB 0) (.const .int 1)))) := by
  simp only [oneTrueE, blistEnv, blistDecl]
  generate
  solve

/-! ## Facts whatever the fields' types

  The match facts sit on the payload's terminal unit, so they are recorded even
  when the last field has no refinement of its own (here, the ⋆-kinded `α`). -/

/-- Snoc lists `slist α = SNil | Snoc (slist α, α)`, with `slen`. -/
def slistDecl : DataDecl :=
  { params := [.star], ctorFields := [("SNil", []), ("Snoc", [.dataL "slist" [Par 0], Par 0])],
    variances := [.co],
    measures := [("slen", [.const 0, .add (.const 1) (.meas "slen" 0)])] }
def slistEnv : DEnv := [("slist", slistDecl)]

theorem slistEnv_wf : slistEnv.wfB = true := by decide

/-- `slength : ∀α. xs:slist α → Int{ν = slen xs}` -/
abbrev slengthTy : Ty :=
  .forall .star (.arrow (.dataL "slist" [Par 0])
    (.refine .int (.fmla (.eq .int (.bvar .int 0) (.mbvar "slen" 1)))))

/-- `Λα. fix go. λxs. case xs of SNil _ => 0
                  | Snoc p => let (t, (x, _)) = p; let r = go t; 1 + r` -/
abbrev slengthE : Exp :=
  .tabs .star (.fix (caseL (.bvar 0)                      -- xs=0 go=1
    [ .iconst 0
    , .split (.bvar 0) (.split (.bvar 0)                  -- u=0 x=1 q=2 t=3 p=4 xs=5 go=6
        (.letin (.app (.bvar 6) (.bvar 3))                -- r = go t
        (.letin (.iconst 1)
        (.add (.bvar 0) (.bvar 1))))) ]))

theorem meas_slength : ∃ κ : KEnv, Check slistEnv κ [] slengthE slengthTy := by
  simp only [slengthE, slistEnv, slistDecl]
  generate
  solve

/-- `option α` with `isSome None = 0`, `isSome (Some x) = 1`. -/
def optMeasEnv : DEnv := [("option", { optionDecl with measures := [("isSome", [.const 0, .const 1])] })]

theorem optMeasEnv_wf : optMeasEnv.wfB = true := by decide

/-- `isSome : ∀α. o:option α → Int{ν = isSome o}`:
    `Λα. λo. case o of None _ => 0 | Some p => let (x, _) = p; 1` -/
abbrev isSomeTy : Ty :=
  .forall .star (.arrow (.dataL "option" [Par 0])
    (.refine .int (.fmla (.eq .int (.bvar .int 0) (.mbvar "isSome" 1)))))
abbrev isSomeE : Exp :=
  .tabs .star (.lam (caseL (.bvar 0) [.iconst 0, .split (.bvar 0) (.iconst 1)]))

theorem meas_isSome : ∃ κ : KEnv, Check optMeasEnv κ [] isSomeE isSomeTy := by
  simp only [isSomeE, optMeasEnv, optionDecl]
  generate
  solve

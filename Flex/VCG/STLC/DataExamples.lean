import Flex.VCG.STLC.Examples

open STLC

/-! # Algebraic data types

  A program is a list of datatype declarations (`DEnv`) followed by an
  expression. A datatype has kinded type parameters and constructors, each with
  one payload type (several fields are a dependent pair `Σ x:t₁. t₂`, so a
  field may be refined in terms of earlier ones). Constructors are applied at
  explicit type arguments (`Exp.ctor C j τs e`), which may contain κ-templates
  for refinements to infer; `Exp.case` matches with one alternative per
  constructor. -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Base.recast Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var

/-- `case e of alts`, with the alternatives as a list. -/
abbrev caseL (e : Exp) (alts : List Exp) : Exp := .case e alts.length alts.get

/-- The (trivially refined) unit payload of a nullary constructor. -/
abbrev UnitT : Ty := .refine .int ttR
abbrev unitE : Exp := .iconst 0
/-- The `i`-th type parameter of a datatype, refined by `r`. -/
abbrev Par (i : Nat) (r : Refinement := ttR) : Ty := .refine (.tbvar i) r
abbrev NatT : Ty := .refine .int (.fmla (.leqI (.const .int 0) (.bvar .int 0)))

/-! ## `option α = None | Some α` -/

def optionDecl : DataDecl := { params := [.star], ctors := [("None", UnitT), ("Some", Par 0)] }
def optionEnv : DEnv := [("option", optionDecl)]

/-- `fromSome : d:Nat → o:option(Nat) → Nat` -/
abbrev fromSomeTy : Ty := .arrow NatT (.arrow (.dataL "option" [NatT]) NatT)
abbrev fromSomeE : Exp := .lam (.lam (caseL (.bvar 0) [.bvar 2, .bvar 0]))

theorem data_fromSome (κ : KEnv) : topVC κ [] fromSomeE fromSomeTy optionEnv := by
  simp [topVC, fromSomeE, fromSomeTy, optionEnv, optionDecl]

/-! ## A refined product: ordered pairs `ord = MkOrd (x : Int, y : Int{x ≤ ν})`

  The second field's refinement mentions the first. Construction checks it;
  destruction assumes it. -/

/-- `Σ x:Int. Int{x ≤ ν}` (`x` is `BVar 1` inside the second component). -/
abbrev ordPayload : Ty :=
  .prod TT (.refine .int (.fmla (.leqI (.bvar .int 1) (.bvar .int 0))))
def ordDecl : DataDecl := { params := [], ctors := [("MkOrd", ordPayload)] }
def ordEnv : DEnv := [("ord", ordDecl)]
abbrev OrdT : Ty := .dataL "ord" []

abbrev TrueB : Ty := .refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.const .bool true)))

/-- `ordOK : ord → Bool{ν = true}`: `case p of MkOrd q => let (x, y) = q in x ≤ y`. -/
abbrev ordOKE : Exp := .lam (caseL (.bvar 0) [.split (.bvar 0) (.leq (.bvar 1) (.bvar 0))])

theorem data_ordOK (κ : KEnv) : topVC κ [] ordOKE (.arrow OrdT TrueB) ordEnv := by
  simp [topVC, ordOKE, ordEnv, ordDecl]

/-- `let a = 3; let b = 5; MkOrd (a, b)` is an `ord` … -/
theorem data_mkOrd (κ : KEnv) : topVC κ []
    (.letin (.iconst 3) (.letin (.iconst 5) (.ctor "ord" 0 [] (.pair (.bvar 1) (.bvar 0)))))
    OrdT ordEnv := by
  simp [topVC, ordEnv, ordDecl]

/-- … but `MkOrd (b, a)` is rejected: its verification condition is false. -/
theorem data_mkOrd_bad (κ : KEnv) : ¬ topVC κ []
    (.letin (.iconst 3) (.letin (.iconst 5) (.ctor "ord" 0 [] (.pair (.bvar 0) (.bvar 1)))))
    OrdT ordEnv := by
  simp [topVC, ordEnv, ordDecl]
  exact ⟨REnv.empty, trivial⟩

/-! ## Polymorphic, recursive lists: `list α = Nil | Cons (α, list α)` -/

/-- `list` applied to one type argument. -/
abbrev ListT (τ : Ty) : Ty := .dataL "list" [τ]
def listDecl : DataDecl :=
  { params := [.star], ctors := [("Nil", UnitT), ("Cons", .prod (Par 0) (ListT (Par 0)))],
    variances := [.co] }
def listEnv : DEnv := [("list", listDecl)]

abbrev nilE (τ : Ty) : Exp := .ctor "list" 0 [τ] unitE
/-- `Cons[τ] (h, t)` (ANF: `h` a variable). -/
abbrev consE (τ : Ty) (h t : Exp) : Exp := .ctor "list" 1 [τ] (.pair h t)

/-- `sumList : list(Nat) → Nat`:
    `fix sum. λxs. case xs of Nil _ => 0 | Cons p => let (h, t) = p in h + sum t` -/
abbrev sumListTy : Ty := .arrow (ListT NatT) NatT
abbrev sumListE : Exp :=
  .fix (caseL (.bvar 0)                                    -- xs=0 self=1
    [ .iconst 0
    , .split (.bvar 0)                                     -- p=0 xs=1 self=2
        (.letin (.app (.bvar 4) (.bvar 0))                 -- t=0 h=1 p=2 xs=3 self=4
          (.add (.bvar 2) (.bvar 0))) ])                   -- r=0 t=1 h=2

theorem data_sumList (κ : KEnv) : topVC κ [] sumListE sumListTy listEnv := by
  simp [topVC, sumListE, sumListTy, listEnv, listDecl]
  intros; omega

/-- Inference: build `[1, 2]` with `Cons[int{k}]` and sum it. The element
    refinement `k` is inferred (it must admit `1` and `2`, and imply `Nat` at
    the call `sum l`, by covariance of `list`). -/
theorem data_sumList_client : ∃ κ : KEnv, Check listEnv κ []
    (.letin (.ann sumListE sumListTy)                    -- sum
    (.letin (.iconst 1)                                  -- one
    (.letin (.iconst 2)                                  -- two
    (.letin (nilE (IntK "k"))                            -- nil
    (.letin (consE (IntK "k") (.bvar 1) (.bvar 0))       -- l1 = Cons(two, nil)
    (.letin (consE (IntK "k") (.bvar 3) (.bvar 0))       -- l2 = Cons(one, l1)
    (.app (.bvar 5) (.bvar 0))))))))                     -- sum l2
    NatT := by
  simp only [sumListE, listEnv, listDecl]
  generate
  zap
  grind

/-! ## Polymorphism + data + recursion: `map : ∀α β:⋆. (α → β) → list α → list β` -/

abbrev mapTy : Ty := .forall .star (.forall .star
  (.arrow (.arrow (Par 1) (Par 0)) (.arrow (ListT (Par 1)) (ListT (Par 0)))))

/-- `Λα. Λβ. λf. fix go. λxs. case xs of
      Nil _  => Nil[β]
      Cons p => let (h, t) = p in let y = f h in let r = go t in Cons[β] (y, r)` -/
abbrev mapE : Exp := .tabs .star (.tabs .star (.lam (.fix (caseL (.bvar 0)
  [ nilE (Par 0)
  , .split (.bvar 0)                            -- t=0 h=1 p=2 xs=3 go=4 f=5
      (.letin (.app (.bvar 5) (.bvar 1))        -- y = f h
      (.letin (.app (.bvar 5) (.bvar 1))        -- r = go t      (y=0 t=1 … go=5)
      (consE (Par 0) (.bvar 1) (.bvar 0)))) ]))))

theorem data_map (κ : KEnv) : topVC κ [] mapE mapTy listEnv := by
  simp [topVC, mapE, mapTy, listEnv, listDecl]

abbrev incNatTy : Ty :=
  .arrow NatT (.refine .int (.fmla (.eq .int (.bvar .int 0) (.add (.bvar .int 1) (.const .int 1)))))
abbrev incNatE : Exp := .lam (.letin (.iconst 1) (.add (.bvar 1) (.bvar 0)))

/-- `λxs. let inc = …; map[Nat][int{k}] inc xs ⇐ list(Nat) → list(Pos)`: the
    result's element refinement `k` is inferred (`1 ≤ ν`). -/
theorem data_map_client : ∃ κ : KEnv, Check listEnv κ []
    (.lam
      (.letin (.ann incNatE incNatTy)                                         -- inc   xs=1
      (.letin (.app (.tapp (.tapp (.ann mapE mapTy) NatT) (IntK "k")) (.bvar 0))  -- map[..] inc
      (.app (.bvar 0) (.bvar 2)))))                                           -- … xs
    (.arrow (ListT NatT) (ListT Pos)) := by
  simp only [mapE, mapTy, listEnv, listDecl]
  generate
  zap
  grind

/-! ## End to end: the declarations are well-formed, and the program is safe -/

theorem listEnv_wf : listEnv.wfB = true := by decide

/-- `sum [1, 2]` (the client above). -/
abbrev sumClientE : Exp :=
  .letin (.ann sumListE sumListTy)
  (.letin (.iconst 1)
  (.letin (.iconst 2)
  (.letin (nilE (IntK "k"))
  (.letin (consE (IntK "k") (.bvar 1) (.bvar 0))
  (.letin (consE (IntK "k") (.bvar 3) (.bvar 0))
  (.app (.bvar 5) (.bvar 0)))))))

/-- Running `sum [1, 2]` never gets stuck, and any value it returns is a
    natural number. -/
theorem data_sumList_safe (n : Nat) :
    ∃ o, Run n sumClientE o ∧ ∀ v m, o = .val v m → ∃ i : Int, v = .iconst i ∧ 0 ≤ i := by
  obtain ⟨κ, h⟩ := data_sumList_client
  have hh := check_to_hastype TEnv.WFBVars.empty
    (by simp [Exp.WFBVars, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar,
              Term.hasBVar])
    (by simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]) h
  obtain ⟨o, hrun, hres⟩ := type_safety listEnv_wf hh n
  refine ⟨o, hrun, fun v m ho => ?_⟩
  have := hres v m ho
  simp only [TyDenote, BaseDen] at this
  obtain ⟨⟨i, rfl⟩, hi⟩ := this
  exact ⟨i, rfl, by simpa [Refinement.interp, Formula.interp, Term.interp] using hi⟩

/-! ## Variance

  `list` is declared covariant (checked against its payloads by `DEnv.wfB`), so
  a `list(Pos)` is a `list(Nat)`. -/

theorem data_sumList_pos (κ : KEnv) : topVC κ [] (.lam (.app (.ann sumListE sumListTy) (.bvar 0)))
    (.arrow (ListT Pos) NatT) listEnv := by
  simp [topVC, sumListE, sumListTy, listEnv, listDecl]
  intro _; constructor <;> intros <;> omega

/-- A contravariant datatype: predicates `pred α = Pred (α → Bool)`. -/
def predDecl : DataDecl :=
  { params := [.star], ctors := [("Pred", .arrow (Par 0) (.refine .bool ttR))],
    variances := [.contra] }
def predEnv : DEnv := [("pred", predDecl)]

theorem predEnv_wf : predEnv.wfB = true := by decide

/-- A predicate on integers is a predicate on naturals (but not conversely). -/
theorem data_pred_contra (κ : KEnv) : topVC κ [] (.lam (.bvar 0))
    (.arrow (.dataL "pred" [TT]) (.dataL "pred" [NatT])) predEnv := by
  simp [topVC, predEnv, predDecl]

theorem data_pred_contra_bad (κ : KEnv) : ¬ topVC κ [] (.lam (.bvar 0))
    (.arrow (.dataL "pred" [NatT]) (.dataL "pred" [TT])) predEnv := by
  simp [topVC, predEnv, predDecl]
  exact ⟨REnv.empty, -1, by omega⟩

/-- Declaring `pred` covariant is rejected by the well-formedness check. -/
theorem predEnv_co_bad : DEnv.wfB [("pred", { predDecl with variances := [.co] })] = false := by
  decide

/-! ## The book's `range` (§7.1.1)

  `range hi lo` returns the integers in `[lo, hi)`, and its type says so:
  `hi:Int → lo:Int → list(Int{lo ≤ ν ∧ ν < hi})`. The `Cons` instance is a
  κ-template over `lo` and `hi` (instances may mention program variables); the
  solver infers `k(lo, hi, ν) := lo ≤ ν ∧ ν < hi`. The empty list is built at
  `Int{false}` and widened by covariance. -/

/-- `Int{lo ≤ ν ∧ ¬(hi ≤ ν)}` with `lo`, `hi` the two enclosing arrow binders. -/
abbrev rangeElem : Ty :=
  .refine .int (.fmla (.and (.leqI (.bvar .int 1) (.bvar .int 0))
                            (.not (.leqI (.bvar .int 2) (.bvar .int 0)))))
abbrev rangeTy : Ty := .arrow TT (.arrow TT (ListT rangeElem))
abbrev FalseInt : Ty := .refine .int (.fmla .ff)

/-- `λhi. fix go. λlo. let c = hi ≤ lo in
      if c then Nil[Int{false}] else let one = 1; let lo1 = lo + one; let rest = go lo1;
      let h = lo; Cons[Int{k(lo, hi, ν)}] (h, rest)`
    (The head is rebound to `h` because the pair rule's first component must not
    occur free in the second component's type, which mentions `lo`.) -/
abbrev rangeE : Exp :=
  .lam (.fix
    (.letin (.leq (.bvar 2) (.bvar 0))                 -- c        lo=1 go=2 hi=3
      (.ite (.bvar 0)
        (nilE FalseInt)
        (.letin (.iconst 1)                            -- one      c=1 lo=2 go=3 hi=4
        (.letin (.add (.bvar 2) (.bvar 0))             -- lo1      one=1 c=2 lo=3 go=4 hi=5
        (.letin (.app (.bvar 4) (.bvar 0))             -- rest     lo1=1 one=2 c=3 lo=4 go=5 hi=6
        (.letin (.bvar 4)                              -- h = lo   rest=1 lo1=2 one=3 c=4 lo=5 go=6 hi=7
          -- in the instance: ν=0 h=1 rest=2 lo1=3 one=4 c=5 lo=6 go=7 hi=8
          (consE (.refine .int (.kapp "k" [⟨.int, .bvar .int 6⟩, ⟨.int, .bvar .int 8⟩,
                                          ⟨.int, .bvar .int 0⟩]))
            (.bvar 0) (.bvar 1)))))))))

theorem data_range : ∃ κ : KEnv, Check listEnv κ [] rangeE rangeTy := by
  simp only [listEnv, listDecl]
  generate
  zap
  grind

/-! ## Path-sensitive filtering: `filterGe : lo:Int → list(Int) → list(Int{lo ≤ ν})`

  The kept elements are exactly those that passed the test, which the branch
  condition records; the `Cons` instance `Int{k(lo, ν)}` is inferred. -/

abbrev filterGeTy : Ty :=
  .arrow TT (.arrow (ListT TT) (ListT (.refine .int (.fmla (.leqI (.bvar .int 2) (.bvar .int 0))))))

/-- `λlo. fix go. λxs. case xs of
      Nil _  => Nil[Int{false}]
      Cons p => let (h, t) = p; let r = go t; let c = lo ≤ h;
                if c then (let h' = h; Cons[Int{k(lo, ν)}] (h', r)) else r` -/
abbrev filterGeE : Exp :=
  .lam (.fix (caseL (.bvar 0)
    [ nilE FalseInt
    , .split (.bvar 0)                                  -- t=0 h=1 p=2 xs=3 go=4 lo=5
        (.letin (.app (.bvar 4) (.bvar 0))              -- r     t=1 h=2 … go=5 lo=6
        (.letin (.leq (.bvar 6) (.bvar 2))              -- c     r=1 t=2 h=3 … lo=7
        (.ite (.bvar 0)
          (.letin (.bvar 3)                             -- h'    c=1 r=2 t=3 h=4 … lo=8
            -- in the instance: ν=0 h'=1 c=2 r=3 t=4 h=5 p=6 xs=7 go=8 lo=9
            (consE (.refine .int (.kapp "k" [⟨.int, .bvar .int 9⟩, ⟨.int, .bvar .int 0⟩]))
              (.bvar 0) (.bvar 2)))
          (.bvar 1)))) ]))

theorem data_filterGe : ∃ κ : KEnv, Check listEnv κ [] filterGeE filterGeTy := by
  simp only [listEnv, listDecl]
  generate
  zap
  grind

/-! ## Polymorphic `append`, instantiated by inference under covariance

  `append : ∀α:⋆. list α → list α → list α`. Appending a `list(Pos)` to a
  `list(Nat)`, the instance `int{k}` must contain both element types and fit the
  result `list(Nat)`: the solver picks `k(ν) := 0 ≤ ν`. -/

abbrev appendTy : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.arrow (ListT (Par 0)) (ListT (Par 0))))

/-- `Λα. fix go. λxs. λys. case xs of
      Nil _  => ys
      Cons p => let (h, t) = p; let g = go t; let r = g ys; Cons[α] (h, r)` -/
abbrev appendE : Exp :=
  .tabs .star (.fix (.lam (caseL (.bvar 1)
    [ .bvar 1
    , .split (.bvar 0)                                  -- t=0 h=1 p=2 ys=3 xs=4 go=5
        (.letin (.app (.bvar 5) (.bvar 0))              -- g = go t
        (.letin (.app (.bvar 0) (.bvar 4))              -- r = g ys   (g=0 t=1 h=2 p=3 ys=4)
        (consE (Par 0) (.bvar 3) (.bvar 0)))) ])))

theorem data_append (κ : KEnv) : topVC κ [] appendE appendTy listEnv := by
  simp [topVC, appendE, appendTy, listEnv, listDecl]

theorem data_append_client : ∃ κ : KEnv, Check listEnv κ []
    (.lam (.lam                                                    -- xs=1 ys=0
      (.letin (.app (.tapp (.ann appendE appendTy) (IntK "k")) (.bvar 1))   -- g = append[k] xs
      (.app (.bvar 0) (.bvar 1)))))                                -- g ys
    (.arrow (ListT Pos) (.arrow (ListT NatT) (ListT NatT))) := by
  simp only [appendE, appendTy, listEnv, listDecl]
  generate
  zap
  grind

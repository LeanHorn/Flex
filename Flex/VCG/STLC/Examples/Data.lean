import Flex.VCG.STLC.Examples.Basic

open STLC

/-! # Algebraic data types

  A program is a list of datatype declarations (`DEnv`) followed by an
  expression. A datatype has kinded type parameters and constructors, each with
  a telescope of fields; the payload is the fields in nested pairs ending in a
  unit, `(f₀, (f₁, ()))` (a dependent pair `Σ x:t₁. t₂`, so a field may be
  refined in terms of earlier ones). Constructors are applied at
  explicit type arguments (`Exp.ctor C j τs e`), which may contain κ-templates
  for refinements to infer; `Exp.case` matches with one alternative per
  constructor.

  Datatypes are declared with `stlc_data`, which also registers the
  constructors with the notation: `Cons[τ] h t` builds the payload
  `(h, (t, ()))`, and a `match` alternative `Cons h t => e` takes it apart
  (`let (h, (t, _)) = payload in e`). -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var

abbrev NatT : Ty := <ty| Int{ν : 0 ≤ ν} |>

/-! ## `option α = None | Some α` -/

stlc_data optionDecl : option (α : ⋆) where
  | None
  | Some (x : α)
def optionEnv : DEnv := [("option", optionDecl)]

/-- `fromSome : d:Nat → o:option(Nat) → Nat` -/
abbrev fromSomeTy : Ty := <ty| ⌜NatT⌝ -> option[⌜NatT⌝] -> ⌜NatT⌝ |>
abbrev fromSomeE : Exp :=
  <| λ d o, match o with
       | None => d
       | Some x => x |>

theorem data_fromSome (κ : KEnv) : topVC κ [] fromSomeE fromSomeTy optionEnv := by
  simp [topVC, fromSomeE, fromSomeTy, optionEnv, optionDecl]

/-! ## A refined product: ordered pairs `ord = MkOrd (x : Int, y : Int{x ≤ ν})`

  The second field's refinement mentions the first. Construction checks it;
  destruction assumes it. -/

stlc_data ordDecl : ord where
  | MkOrd (x : Int) (y : Int{ν : x ≤ ν})
def ordEnv : DEnv := [("ord", ordDecl)]
abbrev OrdT : Ty := <ty| ord |>

abbrev TrueB : Ty := <ty| Bool{ν : ν = true} |>

/-- `ordOK : ord → Bool{ν = true}` -/
abbrev ordOKE : Exp :=
  <| λ p, match p with
       | MkOrd x y => x ≤ y |>

theorem data_ordOK (κ : KEnv) : topVC κ [] ordOKE <ty| ⌜OrdT⌝ -> ⌜TrueB⌝ |> ordEnv := by
  simp [topVC, ordOKE, ordEnv, ordDecl]

/-- `let a = 3; let b = 5; MkOrd (a, b)` is an `ord` … -/
theorem data_mkOrd (κ : KEnv) : topVC κ []
    <| let a = 3 in let b = 5 in MkOrd a b |>
    OrdT ordEnv := by
  simp [topVC, ordEnv, ordDecl]

/-- … but `MkOrd (b, a)` is rejected: its verification condition is false. -/
theorem data_mkOrd_bad (κ : KEnv) : ¬ topVC κ []
    <| let a = 3 in let b = 5 in MkOrd b a |>
    OrdT ordEnv := by
  simp [topVC, ordEnv, ordDecl]
  exact ⟨REnv.empty, trivial⟩

/-! ## Polymorphic, recursive lists: `list α = Nil | Cons (α, list α)` -/

/-- `list` applied to one type argument. -/
stlc_data listDecl : list (+α : ⋆) where
  | Nil
  | Cons (h : α) (t : list[α])
def listEnv : DEnv := [("list", listDecl)]

/-- `sumList : list(Nat) → Nat` -/
abbrev sumListTy : Ty := <ty| list[⌜NatT⌝] -> ⌜NatT⌝ |>
abbrev sumListE : Exp :=
  <| fix sum xs, match xs with
       | Nil => 0
       | Cons h t => let r = sum t in h + r |>

theorem data_sumList (κ : KEnv) : topVC κ [] sumListE sumListTy listEnv := by
  simp [topVC, sumListE, sumListTy, listEnv, listDecl]
  intros; omega

/-- Inference: build `[1, 2]` with `Cons[int{k}]` and sum it. The element
    refinement `k` is inferred (it must admit `1` and `2`, and imply `Nat` at
    the call `sum l`, by covariance of `list`). -/
theorem data_sumList_client : ∃ κ : KEnv, Check listEnv κ []
    <| let sum : ⌜sumListTy⌝ = ⌜sumListE⌝ in
       let one = 1 in let two = 2 in
       let nil = Nil[Int{ν : k ν}] in
       let l1 = Cons[Int{ν : k ν}] two nil in
       let l2 = Cons[Int{ν : k ν}] one l1 in
       sum l2 |>
    NatT := by
  simp only [sumListE, listEnv, listDecl]
  generate
  zap
  grind

/-! ## Polymorphism + data + recursion: `map : ∀α β:⋆. (α → β) → list α → list β` -/

abbrev mapTy : Ty := <ty| ∀ α : ⋆, ∀ β : ⋆, (α -> β) -> list[α] -> list[β] |>

abbrev mapE : Exp :=
  <| Λ α : ⋆, Λ β : ⋆, λ f, fix go xs, match xs with
       | Nil => Nil[β]
       | Cons h t => let y = f h in let r = go t in Cons[β] y r |>

theorem data_map (κ : KEnv) : topVC κ [] mapE mapTy listEnv := by
  simp [topVC, mapE, mapTy, listEnv, listDecl]

abbrev incNatTy : Ty := <ty| (x : Int{ν : 0 ≤ ν}) -> Int{ν : ν = x + 1} |>
abbrev incNatE : Exp := <| λ x, let one = 1 in x + one |>

/-- `λxs. let inc = …; map[Nat][int{k}] inc xs ⇐ list(Nat) → list(Pos)`: the
    result's element refinement `k` is inferred (`1 ≤ ν`). -/
theorem data_map_client : ∃ κ : KEnv, Check listEnv κ []
    <| λ xs, let inc : ⌜incNatTy⌝ = ⌜incNatE⌝ in
         let g = (⌜mapE⌝ : ⌜mapTy⌝)[⌜NatT⌝, Int{ν : k ν}] inc in
         g xs |>
    <ty| list[⌜NatT⌝] -> list[⌜Pos⌝] |> := by
  simp only [mapE, mapTy, listEnv, listDecl]
  generate
  zap
  grind

/-! ## End to end: the declarations are well-formed, and the program is safe -/

theorem listEnv_wf : listEnv.wfB = true := by decide

/-- `sum [1, 2]` (the client above). -/
abbrev sumClientE : Exp :=
  <| let sum : ⌜sumListTy⌝ = ⌜sumListE⌝ in
     let one = 1 in let two = 2 in
     let nil = Nil[Int{ν : k ν}] in
     let l1 = Cons[Int{ν : k ν}] two nil in
     let l2 = Cons[Int{ν : k ν}] one l1 in
     sum l2 |>

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

theorem data_sumList_pos (κ : KEnv) : topVC κ [] <| λ xs, (⌜sumListE⌝ : ⌜sumListTy⌝) xs |>
    <ty| list[⌜Pos⌝] -> ⌜NatT⌝ |> listEnv := by
  simp [topVC, sumListE, sumListTy, listEnv, listDecl]
  intro _; constructor <;> intros <;> omega

/-- A contravariant datatype: predicates `pred α = Pred (α → Bool)`. -/
stlc_data predDecl : pred (-α : ⋆) where
  | Pred (p : α -> Bool)
def predEnv : DEnv := [("pred", predDecl)]

theorem predEnv_wf : predEnv.wfB = true := by decide

/-- A predicate on integers is a predicate on naturals (but not conversely). -/
theorem data_pred_contra (κ : KEnv) : topVC κ [] <| λ p, p |>
    <ty| pred[Int] -> pred[⌜NatT⌝] |> predEnv := by
  simp [topVC, predEnv, predDecl]

theorem data_pred_contra_bad (κ : KEnv) : ¬ topVC κ [] <| λ p, p |>
    <ty| pred[⌜NatT⌝] -> pred[Int] |> predEnv := by
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

/-- `hi:Int → lo:Int → list(Int{lo ≤ ν ∧ ν < hi})` (`ν < hi` is `¬(hi ≤ ν)`). -/
abbrev rangeTy : Ty := <ty| (hi : Int) -> (lo : Int) -> list[Int{ν : lo ≤ ν ∧ ν < hi}] |>

/-- The head is rebound to `h` because the pair rule's first component must not
    occur free in the second component's type, which mentions `lo`. -/
abbrev rangeE : Exp :=
  <| λ hi, fix go lo,
       let c = hi ≤ lo in
       if c then Nil[Int{ν : ⊥}]
       else let one = 1 in let lo1 = lo + one in let rest = go lo1 in
            let h = lo in Cons[Int{ν : k lo hi ν}] h rest |>

theorem data_range : ∃ κ : KEnv, Check listEnv κ [] rangeE rangeTy := by
  simp only [listEnv, listDecl]
  generate
  zap
  grind

/-! ## Path-sensitive filtering: `filterGe : lo:Int → list(Int) → list(Int{lo ≤ ν})`

  The kept elements are exactly those that passed the test, which the branch
  condition records; the `Cons` instance `Int{k(lo, ν)}` is inferred. -/

abbrev filterGeTy : Ty := <ty| (lo : Int) -> list[Int] -> list[Int{ν : lo ≤ ν}] |>

abbrev filterGeE : Exp :=
  <| λ lo, fix go xs, match xs with
       | Nil => Nil[Int{ν : ⊥}]
       | Cons h t =>
           let r = go t in let c = lo ≤ h in
           if c then (let h' = h in Cons[Int{ν : k lo ν}] h' r) else r |>

theorem data_filterGe : ∃ κ : KEnv, Check listEnv κ [] filterGeE filterGeTy := by
  simp only [listEnv, listDecl]
  generate
  zap
  grind

/-! ## Polymorphic `append`, instantiated by inference under covariance

  `append : ∀α:⋆. list α → list α → list α`. Appending a `list(Pos)` to a
  `list(Nat)`, the instance `int{k}` must contain both element types and fit the
  result `list(Nat)`: the solver picks `k(ν) := 0 ≤ ν`. -/

abbrev appendTy : Ty := <ty| ∀ α : ⋆, list[α] -> list[α] -> list[α] |>

abbrev appendE : Exp :=
  <| Λ α : ⋆, fix go xs, λ ys, match xs with
       | Nil => ys
       | Cons h t => let g = go t in let r = g ys in Cons[α] h r |>

theorem data_append (κ : KEnv) : topVC κ [] appendE appendTy listEnv := by
  simp [topVC, appendE, appendTy, listEnv, listDecl]

theorem data_append_client : ∃ κ : KEnv, Check listEnv κ []
    <| λ xs ys, let g = (⌜appendE⌝ : ⌜appendTy⌝)[Int{ν : k ν}] xs in g ys |>
    <ty| list[⌜Pos⌝] -> list[⌜NatT⌝] -> list[⌜NatT⌝] |> := by
  simp only [appendE, appendTy, listEnv, listDecl]
  generate
  zap
  grind

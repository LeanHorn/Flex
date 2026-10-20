import Flex.VCG.STLC.Examples.Measure

open STLC

/-! # Inferring measure specifications with Flex

  The specifications of the recursive functions in `MeasureExamples` are left
  as κ-templates over measures (`k(len ν, len xs)`, …) and inferred from what a
  client needs. The κs are cyclic, so `fix` (predicate abstraction over the
  `@[qualif]` qualifiers, then `grind`) solves them; to the solver, measures are
  plain integer atoms. -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var DataDecl.measBody? Base.constSubst
  TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons caseL

/-- Qualifiers for relations between measures. -/
@[qualif] def QEqM (a b : Int) : Prop := a = b
@[qualif] def QEqAddM (a b c : Int) : Prop := a = b + c

/-! ## `length`: `xs:list α → Int{k(ν, len xs)}`, where the client needs `ν = len xs` -/
abbrev lengthTyK : Ty := <ty| ∀ α : ⋆, (xs : list[α]) -> Int{ν : k ν (len xs)} |>

theorem infer_length : ∃ κ : KEnv, Check lenEnv κ []
    <| let length : ⌜lengthTyK⌝ = ⌜lengthE⌝ in λ xs, length[Int] xs |>
    <ty| (xs : list[Int]) -> Int{ν : ν = len xs} |> := by
  simp only [lengthE, lenEnv, lenListDecl]
  generate
  fix

/-! ## `map`: a κ in a datatype refinement, `list β{k(len ν, len xs)}` -/
abbrev mapTyK : Ty :=
  <ty| ∀ α : ⋆, ∀ β : ⋆, (α -> β) -> (xs : list[α]) -> list[β]{ν : k (len ν) (len xs)} |>

theorem infer_map : ∃ κ : KEnv, Check lenEnv κ []
    <| let map : ⌜mapTyK⌝ = ⌜mapE⌝ in λ f xs, map[Int, Int] f xs |>
    <ty| (Int -> Int) -> (xs : list[Int]) -> list[Int]{ν : len ν = len xs} |> := by
  simp only [mapE, lenEnv, lenListDecl]
  generate
  fix

/-! ## `append`: a three-way relation `k(len ν, len xs, len ys)`; the client needs `len ν = len xs + len ys` -/
abbrev appendTyK : Ty :=
  <ty| ∀ α : ⋆, (xs : list[α]) -> (ys : list[α]) -> list[α]{ν : k (len ν) (len xs) (len ys)} |>

theorem infer_append : ∃ κ : KEnv, Check lenEnv κ []
    <| let append : ⌜appendTyK⌝ = ⌜appendE⌝ in λ xs ys, append[Int] xs ys |>
    <ty| (xs : list[Int]) -> (ys : list[Int]) -> list[Int]{ν : len ν = len xs + len ys} |> := by
  simp only [appendE, lenEnv, lenListDecl]
  generate
  fix

/-! ## The statement of a lemma: `nonneg : xs:list α → Int{k(len xs)}`

  The client `cons` calls `nonneg t` and needs `0 < len (Cons h t)`, i.e. a
  lemma at least as strong as `0 ≤ len t`; the solver finds one that the
  recursion establishes. -/
abbrev nonnegTyK : Ty := <ty| ∀ α : ⋆, (xs : list[α]) -> Int{ν : k (len xs)} |>

theorem infer_nonneg : ∃ κ : KEnv, Check lenEnv κ []
    <| let nonneg : ⌜nonnegTyK⌝ = ⌜nonnegE⌝ in
       Λ α : ⋆, λ h t, let _ = nonneg[α] t in Cons[α] h t |>
    consPosTy := by
  simp only [nonnegE, consPosTy, lenEnv, lenListDecl]
  generate
  fix

/-! ## `mirror`: an inferred height relation (the verification condition contains `ite`) -/
abbrev mirrorTyK : Ty :=
  <ty| ∀ α : ⋆, (t : tree[α]) -> tree[α]{ν : k (height ν) (height t)} |>

theorem infer_mirror : ∃ κ : KEnv, Check htreeEnv κ []
    <| let mirror : ⌜mirrorTyK⌝ = ⌜mirrorE⌝ in λ t, mirror[Int] t |>
    <ty| (t : tree[Int]) -> tree[Int]{ν : height ν = height t} |> := by
  simp only [mirrorE, htreeEnv, htreeDecl]
  generate
  fix

/-! ## `filterGe`: the length bound inferred, alongside the element refinement's κ (`solve` = `zap`, then `fix`) -/
abbrev filterGeTyK : Ty :=
  <ty| (lo : Int) -> (xs : list[Int]) -> list[Int{ν : lo ≤ ν}]{ν : kl (len ν) (len xs)} |>

theorem infer_filterGe : ∃ κ : KEnv, Check lenEnv κ []
    <| let filterGe : ⌜filterGeTyK⌝ = ⌜filterGeE⌝ in λ lo xs, filterGe lo xs |>
    <ty| (lo : Int) -> (xs : list[Int]) -> list[Int{ν : lo ≤ ν}]{ν : len ν ≤ len xs} |> := by
  simp only [filterGeE, lenEnv, lenListDecl]
  generate
  solve

/-! ## `sum` over an integer list (an `Int`-field measure) -/
theorem infer_sum : ∃ κ : KEnv, Check ilistEnv κ []
    <| let go : (xs : ilist) -> Int{ν : k ν (sum xs)} = ⌜sumIListE⌝ in λ xs, go xs |>
    sumIListTy := by
  simp only [sumIListE, ilistEnv, ilistDecl]
  generate
  fix

/-! ## `count` over a list of booleans (a `Bool`-field measure; `ite` in the VC) -/
theorem infer_count : ∃ κ : KEnv, Check blistEnv κ []
    <| let go : (xs : blist) -> Int{ν : k ν (countTrue xs)} = ⌜countE⌝ in λ xs, go xs |>
    countTy := by
  simp only [countE, blistEnv, blistDecl]
  generate
  fix

/-! ## `node`, with the statement of its size lemma inferred -/
theorem infer_node : ∃ κ : KEnv, Check treeEnv κ []
    <| let lemma : ∀ α : ⋆, (t : tree[α]) -> Int{ν : k (size t)} = ⌜sizeNonnegE⌝ in
       Λ α : ⋆, λ l x r, let _ = lemma[α] r in Node[α] l x r |>
    nodeTy := by
  simp only [sizeNonnegE, nodeTy, treeEnv, treeDecl]
  generate
  fix

/-! ## A lemma relating two measures, inferred: the client needs `height t ≤ size t`; the
  induction also needs `0 ≤ height t` (and `0 ≤ size t`), which the solver finds too -/
theorem infer_heightLeSize : ∃ κ : KEnv, Check htreeEnv κ []
    <| let lemma : ∀ α : ⋆, (t : tree[α]) -> Int{ν : k (height t) (size t)} = ⌜sizeNonnegE⌝ in
       λ t, lemma[Int] t |>
    <ty| (t : tree[Int]) -> Int{ν : height t ≤ size t} |> := by
  simp only [sizeNonnegE, htreeEnv, htreeDecl]
  generate
  fix

/-! ## Ordered-list `insert` (polymorphic recursion), adding one element -/

@[qualif] def QSuccM (a b : Int) : Prop := a = b + 1

abbrev insTyK : Ty :=
  <ty| ∀ α : B, α -> (ys : olist[α]) -> olist[α]{ν : k (len ν) (len ys)} |>

theorem infer_insert : ∃ κ : KEnv, Check olistLenEnv κ []
    <| let ins : ⌜insTyK⌝ = ⌜insE⌝ in λ x ys, ins[Int] x ys |>
    <ty| Int -> (ys : olist[Int]) -> olist[Int]{ν : len ν = 1 + len ys} |> := by
  simp only [insE, olistLenEnv, olistLenDecl]
  generate
  solve

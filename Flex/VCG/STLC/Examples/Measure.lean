import Flex.VCG.STLC.Examples.Ord

open STLC

/-! # Measures

  A measure is a structurally recursive function on a datatype, declared with
  one body per constructor (sprite §7.1.3): `len Nil = 0`,
  `len (Cons h t) = 1 + len t`. In refinements it is an uninterpreted function
  of a variable (`Term.mbvar`/`Term.mfvar`, written `len xs`): verification
  conditions only know the equations recorded where a value is built
  (`Cons(h, t) : list{len ν = 1 + len t}`) and where it is matched (in
  `case xs of Cons p ⇒ …`, the payload `p = (h, (t, u))` ends in a unit
  `u : Int{len xs = 1 + len t}`). -/

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
stlc_data lenListDecl : list (+α : ⋆) where
  | Nil
  | Cons (h : α) (t : list[α])
  measure len
  | Nil => 0
  | Cons _ t => 1 + len t
def lenEnv : DEnv := [("list", lenListDecl)]

theorem lenEnv_wf : lenEnv.wfB = true := by decide

/-! ## `length : ∀α. xs:list α → Int{ν = len xs}` -/

abbrev lengthTy : Ty := <ty| ∀ α : ⋆, (xs : list[α]) -> Int{ν : ν = len xs} |>

abbrev lengthE : Exp :=
  <| Λ α : ⋆, fix go xs, match xs with
       | Nil => 0
       | Cons _ t => let r = go t in let one = 1 in one + r |>

/-- The verification condition is the two equations a `case` on `xs` reveals,
    with `len` uninterpreted:
    `len xs = 0 → 0 = len xs` and `len xs = 1 + len t → 1 + len t = len xs`. -/
theorem meas_length : ∃ κ : KEnv, Check lenEnv κ [] lengthE lengthTy := by
  simp only [lengthE, lenEnv, lenListDecl]
  generate
  solve

/-! ## `append : ∀α. xs:list α → ys:list α → list α{len ν = len xs + len ys}` -/

abbrev appendLenTy : Ty :=
  <ty| ∀ α : ⋆, (xs : list[α]) -> (ys : list[α]) -> list[α]{ν : len ν = len xs + len ys} |>

/-- The same program as `appendE` (DataExamples), at the precise type: the
    recursive call `go t ys` returns `len t + len ys` elements, and
    `Cons(h, r)` has one more. -/
theorem meas_append : ∃ κ : KEnv, Check lenEnv κ [] appendE appendLenTy := by
  simp only [appendE, lenEnv, lenListDecl]
  generate
  solve

/-! ## `head : ∀α. xs:list α{0 < len ν} → α` — the `Nil` case is unreachable -/

abbrev headTy : Ty := <ty| ∀ α : ⋆, list[α]{ν : 0 < len ν} -> α |>

abbrev headE : Exp :=
  <| Λ α : ⋆, λ xs, match xs with
       | Nil => unreachable
       | Cons h _ => h |>

theorem meas_head : ∃ κ : KEnv, Check lenEnv κ [] headE headTy := by
  simp only [headE, lenEnv, lenListDecl]
  generate
  solve

/-- Without the precondition, `head` is rejected: nothing rules out `Nil`. -/
theorem meas_head_bad (κ : KEnv) :
    ¬ topVC κ [] headE <ty| ∀ α : ⋆, list[α] -> α |> lenEnv := by
  simp [topVC, headE, lenEnv, lenListDecl]
  exact ⟨{ map := fun _ => .iconst 0 }, rfl⟩

/-! ## `map` preserves the length -/

abbrev mapLenTy : Ty :=
  <ty| ∀ α : ⋆, ∀ β : ⋆, (α -> β) -> (xs : list[α]) -> list[β]{ν : len ν = len xs} |>

theorem meas_map : ∃ κ : KEnv, Check lenEnv κ [] mapE mapLenTy := by
  simp only [mapE, lenEnv, lenListDecl]
  generate
  solve

/-! ## Building a list: `[1, 2]` has length 2 (and not 3) -/

abbrev twoE : Exp :=
  <| let one = 1 in let two = 2 in
     let nil = Nil[Int] in
     let l = Cons[Int] two nil in
     Cons[Int] one l |>

theorem meas_two : ∃ κ : KEnv, Check lenEnv κ [] twoE <ty| list[Int]{ν : len ν = 2} |> := by
  simp only [twoE, lenEnv, lenListDecl]
  generate
  solve

theorem meas_two_bad (κ : KEnv) : ¬ topVC κ [] twoE <ty| list[Int]{ν : len ν = 3} |> lenEnv := by
  simp [topVC, twoE, lenEnv, lenListDecl]
  -- a model of the recorded equations in which `[1, 2]` has length 2
  refine ⟨{ map := fun y => .iconst y.length,
            sorts := { meas := fun _ v => match v with | .iconst n => n - 3 | _ => 0 } }, ?_⟩
  decide

/-! ## Inference over a measure: `κ(len ν)`

  `l = Cons(1, Nil)` is annotated with an unknown refinement of its length,
  `list Int{κ(len ν)}`, and passed to `head`, which needs `0 < len l`. The solver
  infers `κ(n) := 1 ≤ n`. -/

theorem meas_infer : ∃ κ : KEnv, Check lenEnv κ []
    <| let one = 1 in let nil = Nil[Int] in
       let l : list[Int]{ν : k (len ν)} = Cons[Int] one nil in
       (⌜headE⌝ : ⌜headTy⌝)[Int] l |>
    TT := by
  simp only [headE, headTy, lenEnv, lenListDecl]
  generate
  zap
  grind

/-! ## End to end: `head [1, 2]` never reaches its `unreachable` branch -/

abbrev headClientE : Exp :=
  <| let one = 1 in let two = 2 in
     let nil = Nil[Int] in
     let l = Cons[Int] two nil in
     let l' = Cons[Int] one l in
     (⌜headE⌝ : ⌜headTy⌝)[Int] l' |>

theorem meas_headClient_vc : ∃ κ : KEnv, Check lenEnv κ [] headClientE TT := by
  simp only [headClientE, headE, headTy, lenEnv, lenListDecl]
  generate
  solve

/-- Running the client never gets stuck — in particular `head` never takes its
    `Nil` branch, which `len` rules out — and any value it returns is an
    integer. -/
theorem meas_headClient_safe (n : Nat) :
    ∃ o, Run n headClientE o ∧ ∀ v m, o = .val v m → ∃ i : Int, v = .iconst i := by
  obtain ⟨κ, hc⟩ := meas_headClient_vc
  have hh := check_to_hastype ?_ ?_ ?_ hc <;> try decide
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
abbrev nonnegTy : Ty := <ty| ∀ α : ⋆, (xs : list[α]) -> Int{ν : 0 ≤ len xs} |>

abbrev nonnegE : Exp :=
  <| Λ α : ⋆, fix go xs, match xs with
       | Nil => 0
       | Cons _ t => go t |>

/-- The lemma's verification condition is the induction. -/
theorem meas_nonneg : ∃ κ : KEnv, Check lenEnv κ [] nonnegE nonnegTy := by
  simp only [nonnegE, lenEnv, lenListDecl]
  generate
  solve

/-- `cons : ∀α. α → t:list α → list α{0 < len ν}` -/
abbrev consPosTy : Ty := <ty| ∀ α : ⋆, α -> list[α] -> list[α]{ν : 0 < len ν} |>

abbrev consPosE : Exp := <| Λ α : ⋆, λ h t, Cons[α] h t |>

abbrev consPosLemmaE : Exp :=
  <| Λ α : ⋆, λ h t, let _ = (⌜nonnegE⌝ : ⌜nonnegTy⌝)[α] t in Cons[α] h t |>

/-- With the lemma: `len ν = 1 + len t` and `0 ≤ len t` give `0 < len ν`. -/
theorem meas_consPos : ∃ κ : KEnv, Check lenEnv κ [] consPosLemmaE consPosTy := by
  simp only [consPosLemmaE, nonnegE, nonnegTy, lenEnv, lenListDecl]
  generate
  solve

/-- Without the lemma, `t` might have negative length. -/
theorem meas_consPos_bad (κ : KEnv) : ¬ topVC κ [] consPosE consPosTy lenEnv := by
  simp [topVC, consPosE, consPosTy, lenEnv, lenListDecl]
  -- `t` of length -1 makes `Cons(h, t)` have length 0
  refine ⟨{ map := fun y => .iconst y.length,
            sorts := { meas := fun _ v => match v with | .iconst n => n - 3 | _ => 0 } }, ?_⟩
  decide

/-! ## Reading `Int` fields: `sum` of an integer list -/

/-- `ilist = INil | ICons (Int, ilist)` with `sum INil = 0`, `sum (ICons h t) = h + sum t`. -/
stlc_data ilistDecl : ilist where
  | INil
  | ICons (h : Int) (t : ilist)
  measure sum
  | INil => 0
  | ICons h t => h + sum t
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

/-- `sumList : xs:ilist → Int{ν = sum xs}` -/
abbrev sumIListTy : Ty := <ty| (xs : ilist) -> Int{ν : ν = sum xs} |>
abbrev sumIListE : Exp :=
  <| fix go xs, match xs with
       | INil => 0
       | ICons h t => let r = go t in h + r |>

/-- The match records `sum xs = h + sum t`, reading the field `h`. -/
theorem meas_sumIList : ∃ κ : KEnv, Check ilistEnv κ [] sumIListE sumIListTy := by
  simp only [sumIListE, ilistEnv, ilistDecl]
  generate
  solve

/-! ## Trees: `size` -/

/-- `tree α = Leaf | Node (tree α, α, tree α)`, `size Leaf = 0`,
    `size (Node l x r) = 1 + size l + size r`. -/
stlc_data treeDecl : tree (+α : ⋆) where
  | Leaf
  | Node (l : tree[α]) (x : α) (r : tree[α])
  measure size
  | Leaf => 0
  | Node l _ r => 1 + (size l + size r)
def treeEnv : DEnv := [("tree", treeDecl)]

theorem treeEnv_wf : treeEnv.wfB = true := by decide

/-- `mirror : ∀α. t:tree α → tree α{size ν = size t}` -/
abbrev mirrorTy : Ty := <ty| ∀ α : ⋆, (t : tree[α]) -> tree[α]{ν : size ν = size t} |>

abbrev mirrorE : Exp :=
  <| Λ α : ⋆, fix go t, match t with
       | Leaf => Leaf[α]
       | Node l x r => let l' = go l in let r' = go r in Node[α] r' x l' |>

theorem meas_mirror : ∃ κ : KEnv, Check treeEnv κ [] mirrorE mirrorTy := by
  simp only [mirrorE, treeEnv, treeDecl]
  generate
  solve

/-- The lemma `sizeNonneg : ∀α. t:tree α → Int{0 ≤ size t}`: the recursion
    makes one call per subtree (two induction hypotheses). -/
abbrev sizeNonnegTy : Ty := <ty| ∀ α : ⋆, (t : tree[α]) -> Int{ν : 0 ≤ size t} |>
abbrev sizeNonnegE : Exp :=
  <| Λ α : ⋆, fix go t, match t with
       | Leaf => 0
       | Node l _ r => let a = go l in go r |>

theorem meas_sizeNonneg : ∃ κ : KEnv, Check treeEnv κ [] sizeNonnegE sizeNonnegTy := by
  simp only [sizeNonnegE, treeEnv, treeDecl]
  generate
  solve

/-- `node : ∀α. l:tree α → x:α → r:tree α → tree α{size l < size ν}` needs
    `size r ≥ 0`, which the lemma provides. -/
abbrev nodeTy : Ty :=
  <ty| ∀ α : ⋆, (l : tree[α]) -> α -> tree[α] -> tree[α]{ν : size l < size ν} |>
abbrev nodeE : Exp :=
  <| Λ α : ⋆, λ l x r,
       let _ = (⌜sizeNonnegE⌝ : ⌜sizeNonnegTy⌝)[α] r in Node[α] l x r |>

theorem meas_node : ∃ κ : KEnv, Check treeEnv κ [] nodeE nodeTy := by
  simp only [nodeE, sizeNonnegE, sizeNonnegTy, treeEnv, treeDecl]
  generate
  solve

/-! ## `filterGe` shrinks: `len ν ≤ len xs`

  The path-sensitive filter of DataExamples, at a type that also bounds the
  result's length; the element refinement of the `Cons` instance is still
  inferred. -/

abbrev filterGeLenTy : Ty :=
  <ty| (lo : Int) -> (xs : list[Int]) -> list[Int{ν : lo ≤ ν}]{ν : len ν ≤ len xs} |>

theorem meas_filterGe : ∃ κ : KEnv, Check lenEnv κ [] filterGeE filterGeLenTy := by
  simp only [filterGeE, lenEnv, lenListDecl]
  generate
  zap
  grind

/-! ## `insert` into an ordered list adds one element

  The ordered-list `insert` of OrdExamples (polymorphic recursion included), at
  `∀α:B. x:α → ys:olist α → olist α{len ν = 1 + len ys}`. -/

stlc_data olistLenDecl : olist (+α : B) where
  | ONil
  | OCons (x : α) (xs : olist[α{ν : x ≤ ν}])
  measure len
  | ONil => 0
  | OCons _ xs => 1 + len xs
def olistLenEnv : DEnv := [("olist", olistLenDecl)]

theorem olistLenEnv_wf : olistLenEnv.wfB = true := by decide

abbrev insLenTy : Ty :=
  <ty| ∀ α : B, α -> (ys : olist[α]) -> olist[α]{ν : len ν = 1 + len ys} |>

theorem meas_insert : ∃ κ : KEnv, Check olistLenEnv κ [] insE insLenTy := by
  simp only [insE, olistLenEnv, olistLenDecl]
  generate
  solve

/-! ## Conditionals: tree `height`

  `height (Node l x r) = 1 + max (height l) (height r)` uses a conditional
  (`MBody.max a b = if a ≤ b then b else a`), which becomes an `ite` term in
  the logic. -/

/-- Trees with both `size` and `height`. -/
stlc_data htreeDecl : tree (+α : ⋆) where
  | Leaf
  | Node (l : tree[α]) (x : α) (r : tree[α])
  measure size
  | Leaf => 0
  | Node l _ r => 1 + (size l + size r)
  measure height
  | Leaf => 0
  | Node l _ r => 1 + max (height l) (height r)
def htreeEnv : DEnv := [("tree", htreeDecl)]

theorem htreeEnv_wf : htreeEnv.wfB = true := by decide

/-- `mirror` preserves the height too (the `max` swaps its arguments). -/
abbrev mirrorHTy : Ty :=
  <ty| ∀ α : ⋆, (t : tree[α]) -> tree[α]{ν : size ν = size t ∧ height ν = height t} |>

theorem meas_mirrorHeight : ∃ κ : KEnv, Check htreeEnv κ [] mirrorE mirrorHTy := by
  simp only [mirrorE, htreeEnv, htreeDecl]
  generate
  solve

/-- A lemma relating two measures, `0 ≤ height t ≤ size t`, by recursion on
    both subtrees (the program is `sizeNonneg`'s). -/
abbrev heightLeSizeTy : Ty :=
  <ty| ∀ α : ⋆, (t : tree[α]) -> Int{ν : 0 ≤ height t ∧ height t ≤ size t} |>

theorem meas_heightLeSize : ∃ κ : KEnv, Check htreeEnv κ [] sizeNonnegE heightLeSizeTy := by
  simp only [sizeNonnegE, htreeEnv, htreeDecl]
  generate
  solve

/-! ## Reading `Bool` fields: `countTrue`

  `iteB i t e` branches on the `Bool` field `i` (`and`/`or`/`not` of fields by
  nesting); it becomes an `ite` on that field in the logic. -/

/-- `blist = BNil | BCons (Bool, blist)` with `countTrue BNil = 0`,
    `countTrue (BCons b t) = (if b then 1 else 0) + countTrue t`. -/
stlc_data blistDecl : blist where
  | BNil
  | BCons (b : Bool) (t : blist)
  measure countTrue
  | BNil => 0
  | BCons b t => if b then 1 + countTrue t else countTrue t
def blistEnv : DEnv := [("blist", blistDecl)]

theorem blistEnv_wf : blistEnv.wfB = true := by decide

/-- `count : xs:blist → Int{ν = countTrue xs}` -/
abbrev countTy : Ty := <ty| (xs : blist) -> Int{ν : ν = countTrue xs} |>
abbrev countE : Exp :=
  <| fix go xs, match xs with
       | BNil => 0
       | BCons b t => let r = go t in if b then (let one = 1 in one + r) else r |>

/-- The match records `countTrue xs = (if b then 1 + countTrue t else countTrue t)`;
    the branch on `b` picks the matching side. -/
theorem meas_count : ∃ κ : KEnv, Check blistEnv κ [] countE countTy := by
  simp only [countE, blistEnv, blistDecl]
  generate
  solve

/-- `[true, false]` has exactly one `true`. -/
abbrev oneTrueE : Exp :=
  <| let tt = true in let ff = false in
     let n = BNil in
     let l = BCons ff n in
     BCons tt l |>

theorem meas_oneTrue : ∃ κ : KEnv, Check blistEnv κ [] oneTrueE <ty| blist{ν : countTrue ν = 1} |> := by
  simp only [oneTrueE, blistEnv, blistDecl]
  generate
  solve

/-! ## Facts whatever the fields' types

  The match facts sit on the payload's terminal unit, so they are recorded even
  when the last field has no refinement of its own (here, the ⋆-kinded `α`). -/

/-- Snoc lists `slist α = SNil | Snoc (slist α, α)`, with `slen`. -/
stlc_data slistDecl : slist (+α : ⋆) where
  | SNil
  | Snoc (t : slist[α]) (x : α)
  measure slen
  | SNil => 0
  | Snoc t _ => 1 + slen t
def slistEnv : DEnv := [("slist", slistDecl)]

theorem slistEnv_wf : slistEnv.wfB = true := by decide

/-- `slength : ∀α. xs:slist α → Int{ν = slen xs}` -/
abbrev slengthTy : Ty := <ty| ∀ α : ⋆, (xs : slist[α]) -> Int{ν : ν = slen xs} |>

abbrev slengthE : Exp :=
  <| Λ α : ⋆, fix go xs, match xs with
       | SNil => 0
       | Snoc t _ => let r = go t in let one = 1 in one + r |>

theorem meas_slength : ∃ κ : KEnv, Check slistEnv κ [] slengthE slengthTy := by
  simp only [slengthE, slistEnv, slistDecl]
  generate
  solve

/-- `option α` with `isSome None = 0`, `isSome (Some x) = 1`. -/
stlc_data optMeasDecl : option (α : ⋆) where
  | None
  | Some (x : α)
  measure isSome
  | None => 0
  | Some _ => 1
def optMeasEnv : DEnv := [("option", optMeasDecl)]

theorem optMeasEnv_wf : optMeasEnv.wfB = true := by decide

/-- `isSome : ∀α. o:option α → Int{ν = isSome o}` -/
abbrev isSomeTy : Ty := <ty| ∀ α : ⋆, (o : option[α]) -> Int{ν : ν = isSome o} |>
abbrev isSomeE : Exp :=
  <| Λ α : ⋆, λ o, match o with
       | None => 0
       | Some _ => 1 |>

theorem meas_isSome : ∃ κ : KEnv, Check optMeasEnv κ [] isSomeE isSomeTy := by
  simp only [isSomeE, optMeasEnv, optMeasDecl]
  generate
  solve

import Flex.VCG.STLC.Examples.Data

open STLC

/-! # Ordered sorts and polymorphic recursion: the book's ordered lists (§7.1.2)

  `olist α = ONil | OCons (x : α, olist(α{x ≤ ν}))` compares values of an
  *abstract* type `α`. Two orthogonal extensions make it (and `insert`/`isort`)
  go through; neither is specific to lists.

  * **Ordered sorts.** Comparison is polymorphic, exactly like equality: the
    logic has `Formula.leq b` at every sort, and `Exp.leq` types at every
    *comparable* sort — `Int`, `Bool` and `B`-kinded type variables
    (`Synth.leq_var`). As in *Mechanizing Refinement Types*, a type-variable
    sort stands for the base sort of its instances — `Int` or `Bool` — and is
    read at that base (`Base.resolve`), so `≤` at `α` is just `≤` at `Int` or
    at `Bool` (`false < true`). A verification condition for polymorphic code
    must hold for either choice; `split_sorts` splits it into an `Int` goal and
    a `Bool` goal. Types stay erased: a `B`-kinded variable only ever holds ints
    or only bools, whose runtime tags already determine the order, so the
    operational comparison (`Val.leb?`) needs no type information.

  * **Polymorphic recursion.** In `insert`, the recursive call inserts into the
    tail `olist(α{y ≤ ν})`, i.e. at a *different instance* of `α`. `Check.fix`
    binds the function's own name at its annotation generalized over type
    variables the context does not mention (`Ty.gen`), so recursive calls may
    instantiate it (`f[τ]`). The VC generator generalizes when the body
    type-applies the recursive name, and otherwise keeps the monomorphic rule.
    Soundness is the usual Löb induction on the step index, over every
    re-interpretation of the generalized variables (`TyEnvSem.Reinterp`,
    `TyDenote.gen_intro`).

  Type arguments, of constructors and of type applications alike, may mention
  program variables (`ins[α{y ≤ ν}]`). -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons

/-! ## Polymorphic comparison: `max` -/

/-- `max : ∀α:B. x:α → y:α → α{x ≤ ν ∧ y ≤ ν}` -/
abbrev maxTy : Ty := <ty| ∀ α : B, (x : α) -> (y : α) -> α{ν : x ≤ ν ∧ y ≤ ν} |>
abbrev maxE : Exp := <| Λ α : B, λ x y, let c = x ≤ y in if c then y else x |>

/-- The VC is reflexivity and totality of `≤`, at `Int` and at `Bool`. -/
theorem ord_max (κ : KEnv) : topVC κ [] maxE maxTy := by
  simp [topVC]
  split_sorts <;> grind

/-- At `Bool`, the abstract order is `false < true`: `max[Bool] false true` is `true`. -/
theorem ord_max_bool (κ : KEnv) : topVC κ []
    <| let ff = false in let tt = true in (⌜maxE⌝ : ⌜maxTy⌝)[Bool] ff tt |>
    TrueB := by
  simp [topVC]
  split_sorts <;> grind

/-- Comparison is only available at comparable sorts: a `⋆`-kinded variable may
    hold functions. -/
theorem ord_leq_star_bad (κ : KEnv) : ¬ topVC κ []
    <| Λ α : ⋆, λ x y, x ≤ y |>
    <ty| ∀ α : ⋆, α -> α -> Bool |> := by
  simp [topVC]

/-! ## Ordered lists -/

/-- `olist α = ONil | OCons (x : α, olist(α{x ≤ ν}))`, with `α : B` (comparable)
    and covariant. -/
stlc_data olistDecl : olist (+α : B) where
  | ONil
  | OCons (x : α) (xs : olist[α{ν : x ≤ ν}])
def olistEnv : DEnv := [("olist", olistDecl)]

theorem olistEnv_wf : olistEnv.wfB = true := by decide

/-- `okList = OCons(0, OCons(1, OCons(2, ONil)))`, with the inner instances
    `Int{k₁}`, `Int{k₂}` inferred. -/
abbrev okListE : Exp :=
  <| let a = 0 in let b = 1 in let c = 2 in
     let n = ONil[Int{ν : ⊥}] in
     let l₂ = OCons[Int{ν : k2 ν}] c n in
     let l₁ = OCons[Int{ν : k1 ν}] b l₂ in
     OCons[Int] a l₁ |>

theorem ord_okList : ∃ κ : KEnv, Check olistEnv κ [] okListE <ty| olist[Int] |> := by
  simp only [olistEnv, olistDecl]
  generate
  zap
  grind

/-- `badList = OCons(0, OCons(2, OCons(1, ONil)))` -/
abbrev badListE : Exp :=
  <| let a = 0 in let b = 2 in let c = 1 in
     let n = ONil[Int{ν : ⊥}] in
     let l₂ = OCons[Int{ν : k2 ν}] c n in
     let l₁ = OCons[Int{ν : k1 ν}] b l₂ in
     OCons[Int] a l₁ |>

/-- … is rejected, whatever the instances: no κ makes its VC true. -/
theorem ord_badList (κ : KEnv) : ¬ topVC κ [] badListE <ty| olist[Int] |> olistEnv := by
  simp [topVC, olistEnv, olistDecl]
  refine ⟨REnv.empty, fun h₁ _ h => ?_⟩
  have := (h 1 h₁).2
  omega

/-! ## `insert` (polymorphic recursion) -/

abbrev insTy : Ty := <ty| ∀ α : B, α -> olist[α] -> olist[α] |>

/-- Fig. 7.1. The recursive call is at `α{y ≤ ν}`: the tail's elements are all
    `≥ y`. -/
abbrev insE : Exp :=
  <| Λ α : B, fix ins x, λ ys, match ys with
       | ONil => let tl = ONil[α{ν : x ≤ ν}] in OCons[α] x tl
       | OCons y ys' =>
           let c = x ≤ y in
           if c then (let tl = OCons[α{ν : x ≤ ν}] y ys' in OCons[α] x tl)
           else (let g = ins[α{ν : y ≤ ν}] x in let tl = g ys' in OCons[α] y tl) |>

/-- The VC is totality and transitivity of `≤`, at `Int` and at `Bool`. -/
theorem ord_insert (κ : KEnv) : topVC κ [] insE insTy olistEnv := by
  simp [topVC, olistEnv, olistDecl]
  split_sorts <;> grind

/-- With a monomorphic recursive call (`ins x ys'`, at `α` itself) the tail is
    only an `olist(α)`, which is not an `olist(α{y ≤ ν})`: rejected. -/
abbrev insMonoE : Exp :=
  <| Λ α : B, fix ins x, λ ys, match ys with
       | ONil => let tl = ONil[α{ν : x ≤ ν}] in OCons[α] x tl
       | OCons y ys' =>
           let c = x ≤ y in
           if c then (let tl = OCons[α{ν : x ≤ ν}] y ys' in OCons[α] x tl)
           else (let g = ins x in let tl = g ys' in OCons[α] y tl) |>

theorem ord_insert_mono_bad (κ : KEnv) : ¬ topVC κ [] insMonoE insTy olistEnv := by
  simp [topVC, olistEnv, olistDecl]
  exact ⟨REnv.empty, (1 : Int), (0 : Int), fun h => absurd (h (by decide) (-1 : Int)) (by decide)⟩

/-! ## Insertion sort -/

def sortEnv : DEnv := [("list", listDecl), ("olist", olistDecl)]
theorem sortEnv_wf : sortEnv.wfB = true := by decide

abbrev isortTy : Ty := <ty| ∀ α : B, list[α] -> olist[α] |>

abbrev isortE : Exp :=
  <| let ins : ⌜insTy⌝ = ⌜insE⌝ in
     Λ α : B, fix sort xs, match xs with
       | Nil => ONil[α]
       | Cons h t => let s = sort t in let g = ins[α] h in g s |>

theorem ord_isort (κ : KEnv) : topVC κ [] isortE isortTy sortEnv := by
  simp [topVC, sortEnv, olistDecl, listDecl]
  split_sorts <;> grind

/-! ## Using the invariant: the first two elements of an `olist` are in order

  A client, polymorphic in `α`, compares two elements of an ordered list — at
  the abstract sort — and the type system knows the answer. -/

abbrev headsTy : Ty := <ty| ∀ α : B, olist[α] -> Bool{ν : ν = true} |>

abbrev headsOrderedE : Exp :=
  <| Λ α : B, λ l, match l with
       | ONil => true
       | OCons x r => match r with
           | ONil => true
           | OCons y _ => x ≤ y |>

theorem ord_headsOrdered (κ : KEnv) : topVC κ [] headsOrderedE headsTy olistEnv := by
  simp [topVC, olistEnv, olistDecl]

/-! ## End to end: sorting `[3, 1, 2]` and checking its first two elements

  The program instantiates `isort` and `headsOrdered` at `Int`. Its type
  `Bool{ν = true}` is checked by the VC generator, and type safety then says
  that running it never gets stuck and can only return `true`. -/

abbrev sortClientE : Exp :=
  <| let sort : ⌜isortTy⌝ = ⌜isortE⌝ in
     let heads : ⌜headsTy⌝ = ⌜headsOrderedE⌝ in
     let a = 3 in let b = 1 in let c = 2 in
     let nil = Nil[Int] in
     let l₁ = Cons[Int] c nil in           -- [2]
     let l₂ = Cons[Int] b l₁ in            -- [1, 2]
     let l₃ = Cons[Int] a l₂ in            -- [3, 1, 2]
     let s = sort[Int] l₃ in
     heads[Int] s |>

theorem ord_sortClient_vc (κ : KEnv) : topVC κ [] sortClientE TrueB sortEnv := by
  simp [topVC, sortEnv, olistDecl, listDecl]
  split_sorts <;> grind

theorem ord_sortClient_safe (n : Nat) :
    ∃ o, Run n sortClientE o ∧ ∀ v m, o = .val v m → v = .bconst true := by
  have hh := topVC_decl_sound (fun _ _ => True) sortClientE TrueB ?_ ?_ (ord_sortClient_vc _)
    <;> try decide
  obtain ⟨o, hrun, hres⟩ := type_safety sortEnv_wf hh n
  refine ⟨o, hrun, fun v m ho => ?_⟩
  have := hres v m ho
  simp only [TyDenote, BaseDen] at this
  obtain ⟨⟨c, rfl⟩, hc⟩ := this
  simpa [Refinement.interp, Formula.interp, Term.interp, REnv.getBV] using hc

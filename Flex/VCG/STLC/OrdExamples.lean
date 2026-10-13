import Flex.VCG.STLC.DataExamples

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

/-- `x ≤ ν` at sort `b`, with `x` the de Bruijn index `i` (ν is 0). -/
abbrev geR (b : Base) (i : Nat) : Refinement := .fmla (.leq b (.bvar b i) (.bvar b 0))

/-! ## Polymorphic comparison: `max` -/

/-- `max : ∀α:B. x:α → y:α → α{x ≤ ν ∧ y ≤ ν}` -/
abbrev maxTy : Ty := .forall .B (.arrow (Par 0) (.arrow (Par 0)
  (Par 0 (.fmla (.and (.leq (.tbvar 0) (.bvar (.tbvar 0) 2) (.bvar (.tbvar 0) 0))
                      (.leq (.tbvar 0) (.bvar (.tbvar 0) 1) (.bvar (.tbvar 0) 0)))))))
/-- `Λα. λx. λy. let c = x ≤ y in if c then y else x` -/
abbrev maxE : Exp := .tabs .B (.lam (.lam
  (.letin (.leq (.bvar 1) (.bvar 0)) (.ite (.bvar 0) (.bvar 1) (.bvar 2)))))

/-- The VC is reflexivity and totality of `≤`, at `Int` and at `Bool`. -/
theorem ord_max (κ : KEnv) : topVC κ [] maxE maxTy := by
  simp [topVC]
  split_sorts <;> grind

/-- At `Bool`, the abstract order is `false < true`: `max[Bool] false true` is `true`. -/
theorem ord_max_bool (κ : KEnv) : topVC κ []
    (.letin (.bconst false) (.letin (.bconst true)
      (.app (.app (.tapp (.ann maxE maxTy) BoolT) (.bvar 1)) (.bvar 0))))
    TrueB := by
  simp [topVC]
  split_sorts <;> grind

/-- Comparison is only available at comparable sorts: a `⋆`-kinded variable may
    hold functions. -/
theorem ord_leq_star_bad (κ : KEnv) : ¬ topVC κ []
    (.tabs .star (.lam (.lam (.leq (.bvar 1) (.bvar 0)))))
    (.forall .star (.arrow (Par 0) (.arrow (Par 0) BoolT))) := by
  simp [topVC]

/-! ## Ordered lists -/

abbrev OListT (τ : Ty) : Ty := .dataL "olist" [τ]
/-- `olist α = ONil | OCons (x : α, olist(α{x ≤ ν}))`, with `α : B` (comparable)
    and covariant. -/
def olistDecl : DataDecl :=
  { params := [.B],
    ctors := [("ONil", UnitT), ("OCons", .prod (Par 0) (OListT (Par 0 (geR (.tbvar 0) 1))))],
    variances := [.co] }
def olistEnv : DEnv := [("olist", olistDecl)]

abbrev onilE (τ : Ty) : Exp := .ctor "olist" 0 [τ] unitE
/-- `OCons[τ] (h, t)` (ANF: `h` a variable). -/
abbrev oconsE (τ : Ty) (h t : Exp) : Exp := .ctor "olist" 1 [τ] (.pair h t)

theorem olistEnv_wf : olistEnv.wfB = true := by decide

/-- `okList = OCons(0, OCons(1, OCons(2, ONil)))`, with the inner instances
    `Int{k₁}`, `Int{k₂}` inferred. -/
abbrev okListE : Exp :=
  .letin (.iconst 0) (.letin (.iconst 1) (.letin (.iconst 2)   -- c=0 b=1 a=2
  (.letin (onilE FalseInt)                                       -- n
  (.letin (oconsE (IntK "k2") (.bvar 1) (.bvar 0))               -- l₂ = OCons(c, n)
  (.letin (oconsE (IntK "k1") (.bvar 3) (.bvar 0))               -- l₁ = OCons(b, l₂)
  (oconsE TT (.bvar 5) (.bvar 0)))))))                           -- OCons(a, l₁)

theorem ord_okList : ∃ κ : KEnv, Check olistEnv κ [] okListE (OListT TT) := by
  simp only [olistEnv, olistDecl]
  generate
  zap
  grind

/-- `badList = OCons(0, OCons(2, OCons(1, ONil)))` -/
abbrev badListE : Exp :=
  .letin (.iconst 0) (.letin (.iconst 2) (.letin (.iconst 1)
  (.letin (onilE FalseInt)
  (.letin (oconsE (IntK "k2") (.bvar 1) (.bvar 0))
  (.letin (oconsE (IntK "k1") (.bvar 3) (.bvar 0))
  (oconsE TT (.bvar 5) (.bvar 0)))))))

/-- … is rejected, whatever the instances: no κ makes its VC true. -/
theorem ord_badList (κ : KEnv) : ¬ topVC κ [] badListE (OListT TT) olistEnv := by
  simp [topVC, olistEnv, olistDecl]
  refine ⟨REnv.empty, fun h₁ _ h => ?_⟩
  have := (h 1 h₁).2
  omega

/-! ## `insert` (polymorphic recursion) -/

abbrev insTy : Ty := .forall .B (.arrow (Par 0) (.arrow (OListT (Par 0)) (OListT (Par 0))))

/-- Fig. 7.1:
    `Λα. fix ins. λx. λys. case ys of
       ONil _ => let tl = ONil[α{x ≤ ν}]; OCons[α] (x, tl)
       OCons p => let (y, ys') = p; let c = x ≤ y;
                  if c then let tl = OCons[α{x ≤ ν}] (y, ys'); OCons[α] (x, tl)
                  else let g = ins[α{y ≤ ν}] x; let tl = g ys'; OCons[α] (y, tl)`
    The recursive call is at `α{y ≤ ν}`: the tail's elements are all `≥ y`. -/
abbrev insE : Exp := .tabs .B (.fix (.lam                    -- ys=0 x=1 ins=2
  (caseL (.bvar 0)
    [ -- in the instance: ν=0 u=1 ys=2 x=3
      .letin (onilE (Par 0 (geR (.tbvar 0) 3)))              -- tl     u=1 ys=2 x=3
        (oconsE (Par 0) (.bvar 3) (.bvar 0))
    , .split (.bvar 0)                                       -- ys'=0 y=1 p=2 ys=3 x=4 ins=5
        (.letin (.leq (.bvar 4) (.bvar 1))                   -- c      ys'=1 y=2 … x=5 ins=6
          (.ite (.bvar 0)
            -- in the instance: ν=0 c=1 ys'=2 y=3 p=4 ys=5 x=6
            (.letin (oconsE (Par 0 (geR (.tbvar 0) 6)) (.bvar 2) (.bvar 1))   -- tl
              (oconsE (Par 0) (.bvar 6) (.bvar 0)))
            -- in the instance: ν=0 c=1 ys'=2 y=3
            (.letin (.app (.tapp (.bvar 6) (Par 0 (geR (.tbvar 0) 3))) (.bvar 5))  -- g
              (.letin (.app (.bvar 0) (.bvar 2))             -- tl     g=1 c=2 ys'=3 y=4
                (oconsE (Par 0) (.bvar 4) (.bvar 0)))))) ])))

/-- The VC is totality and transitivity of `≤`, at `Int` and at `Bool`. -/
theorem ord_insert (κ : KEnv) : topVC κ [] insE insTy olistEnv := by
  simp [topVC, olistEnv, olistDecl]
  split_sorts <;> grind

/-- With a monomorphic recursive call (`ins x ys'`, at `α` itself) the tail is
    only an `olist(α)`, which is not an `olist(α{y ≤ ν})`: rejected. -/
abbrev insMonoE : Exp := .tabs .B (.fix (.lam
  (caseL (.bvar 0)
    [ .letin (onilE (Par 0 (geR (.tbvar 0) 3)))
        (oconsE (Par 0) (.bvar 3) (.bvar 0))
    , .split (.bvar 0)
        (.letin (.leq (.bvar 4) (.bvar 1))
          (.ite (.bvar 0)
            (.letin (oconsE (Par 0 (geR (.tbvar 0) 6)) (.bvar 2) (.bvar 1))
              (oconsE (Par 0) (.bvar 6) (.bvar 0)))
            (.letin (.app (.bvar 6) (.bvar 5))
              (.letin (.app (.bvar 0) (.bvar 2))
                (oconsE (Par 0) (.bvar 4) (.bvar 0)))))) ])))

theorem ord_insert_mono_bad (κ : KEnv) : ¬ topVC κ [] insMonoE insTy olistEnv := by
  simp [topVC, olistEnv, olistDecl]
  exact ⟨REnv.empty, (1 : Int), (0 : Int), fun h => absurd (h (by decide) (-1 : Int)) (by decide)⟩

/-! ## Insertion sort -/

def sortEnv : DEnv := [("list", listDecl), ("olist", olistDecl)]
theorem sortEnv_wf : sortEnv.wfB = true := by decide

abbrev isortTy : Ty := .forall .B (.arrow (ListT (Par 0)) (OListT (Par 0)))

/-- `let ins = (insE : insTy) in
     Λα. fix sort. λxs. case xs of
       Nil _  => ONil[α]
       Cons p => let (h, t) = p; let s = sort t; let g = ins[α] h; g s` -/
abbrev isortE : Exp :=
  .letin (.ann insE insTy)                                   -- ins
  (.tabs .B (.fix                                            -- xs=0 sort=1 ins=2
     (caseL (.bvar 0)
       [ onilE (Par 0)
       , .split (.bvar 0)                                    -- t=0 h=1 p=2 xs=3 sort=4 ins=5
           (.letin (.app (.bvar 4) (.bvar 0))                -- s
             (.letin (.app (.tapp (.bvar 6) (Par 0)) (.bvar 2))   -- g    s=1 t=2 h=3 … ins=7
               (.app (.bvar 0) (.bvar 1)))) ])))

theorem ord_isort (κ : KEnv) : topVC κ [] isortE isortTy sortEnv := by
  simp [topVC, sortEnv, olistDecl, listDecl]
  split_sorts <;> grind

/-! ## Using the invariant: the first two elements of an `olist` are in order

  A client, polymorphic in `α`, compares two elements of an ordered list — at
  the abstract sort — and the type system knows the answer. -/

abbrev headsTy : Ty := .forall .B (.arrow (OListT (Par 0)) TrueB)

/-- `Λα. λl. case l of ONil _ => true
                     | OCons p => let (x, r) = p in case r of
                         ONil _ => true | OCons q => let (y, _) = q in x ≤ y` -/
abbrev headsOrderedE : Exp := .tabs .B (.lam
  (caseL (.bvar 0)
    [ .bconst true
    , .split (.bvar 0)                                       -- r=0 x=1 p=2 l=3
        (caseL (.bvar 0)
          [ .bconst true
          , .split (.bvar 0) (.leq (.bvar 4) (.bvar 1)) ]) ]))  -- r'=0 y=1 q=2 r=3 x=4

theorem ord_headsOrdered (κ : KEnv) : topVC κ [] headsOrderedE headsTy olistEnv := by
  simp [topVC, olistEnv, olistDecl]

/-! ## End to end: sorting `[3, 1, 2]` and checking its first two elements

  The program instantiates `isort` and `headsOrdered` at `Int`. Its type
  `Bool{ν = true}` is checked by the VC generator, and type safety then says
  that running it never gets stuck and can only return `true`. -/

abbrev sortClientE : Exp :=
  .letin (.ann isortE isortTy)                               -- sort
  (.letin (.ann headsOrderedE headsTy)                       -- heads
  (.letin (.iconst 3) (.letin (.iconst 1) (.letin (.iconst 2)
  (.letin (nilE TT)
  (.letin (consE TT (.bvar 1) (.bvar 0))                     -- [2]
  (.letin (consE TT (.bvar 3) (.bvar 0))                     -- [1, 2]
  (.letin (consE TT (.bvar 5) (.bvar 0))                     -- [3, 1, 2]     heads=7 sort=8
  (.letin (.app (.tapp (.bvar 8) TT) (.bvar 0))              -- s = sort[Int] [3, 1, 2]
  (.app (.tapp (.bvar 8) TT) (.bvar 0)))))))))))             -- heads[Int] s

theorem ord_sortClient_vc (κ : KEnv) : topVC κ [] sortClientE TrueB sortEnv := by
  simp [topVC, sortEnv, olistDecl, listDecl]
  split_sorts <;> grind

theorem ord_sortClient_safe (n : Nat) :
    ∃ o, Run n sortClientE o ∧ ∀ v m, o = .val v m → v = .bconst true := by
  have hh := topVC_decl_sound (fun _ _ => True) sortClientE TrueB
    (by simp [Exp.WFBVars, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar,
              Term.hasBVar])
    (by simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar])
    (ord_sortClient_vc _)
  obtain ⟨o, hrun, hres⟩ := type_safety sortEnv_wf hh n
  refine ⟨o, hrun, fun v m ho => ?_⟩
  have := hres v m ho
  simp only [TyDenote, BaseDen] at this
  obtain ⟨⟨c, rfl⟩, hc⟩ := this
  simpa [Refinement.interp, Formula.interp, Term.interp, REnv.getBV] using hc

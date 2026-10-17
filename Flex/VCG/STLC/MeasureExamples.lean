import Flex.VCG.STLC.DataExamples

open STLC

/-! # Measures

  A measure is a structurally recursive function on a datatype, declared with
  one body per constructor (sprite §7.1.3): `len Nil = 0`,
  `len (Cons h t) = 1 + len t`. In refinements it is an uninterpreted function
  of a variable (`Term.mbvar`/`Term.mfvar`): verification conditions only know
  the equations recorded where a value is built (`Cons(h, t) : list{len ν = 1 + len t}`)
  and where it is matched (in `case xs of Cons p ⇒ …` with `p = (h, t)`,
  `t : list{len xs = 1 + len ν}`). -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var DataDecl.measBody? Base.constSubst

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

/-- `Λα. fix go. λxs. case xs of Nil _ => 0 | Cons p => let (h, t) = p; let r = go t; 1 + r` -/
abbrev lengthE : Exp :=
  .tabs .star (.fix (caseL (.bvar 0)                      -- xs=0 go=1
    [ .iconst 0
    , .split (.bvar 0)                                    -- t=0 h=1 p=2 xs=3 go=4
        (.letin (.app (.bvar 4) (.bvar 0))                -- r = go t
        (.letin (.iconst 1)                               -- one   (r=1 …)
        (.add (.bvar 0) (.bvar 1)))) ]))

/-- The verification condition is the two equations a `case` on `xs` reveals,
    with `len` uninterpreted:
    `len xs = 0 → 0 = len xs` and `len xs = 1 + len t → 1 + len t = len xs`. -/
theorem meas_length (κ : KEnv) : topVC κ [] lengthE lengthTy lenEnv := by
  simp [topVC, lengthE, lengthTy, lenEnv, lenListDecl, listDecl]
  intro γ; constructor <;> intros <;> omega

/-! ## `append : ∀α. xs:list α → ys:list α → list α{len ν = len xs + len ys}` -/

abbrev appendLenTy : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.arrow (ListT (Par 0))
    (ListLen (Par 0) (.add (lenB 2) (lenB 1)))))

/-- The same program as `appendE` (DataExamples), at the precise type: the
    recursive call `go t ys` returns `len t + len ys` elements, and
    `Cons(h, r)` has one more. -/
theorem meas_append (κ : KEnv) : topVC κ [] appendE appendLenTy lenEnv := by
  simp [topVC, appendE, appendLenTy, lenEnv, lenListDecl, listDecl]
  intro γ; constructor <;> intros <;> omega

/-! ## `head : ∀α. xs:list α{0 < len ν} → α` — the `Nil` case is unreachable -/

abbrev headTy : Ty :=
  .forall .star (.arrow (.dataL "list" [Par 0] (.fmla (.not (.leqI (lenB 0) (.const .int 0)))))
    (Par 0))

/-- `Λα. λxs. case xs of Nil _ => unreachable | Cons p => let (h, t) = p; h` -/
abbrev headE : Exp :=
  .tabs .star (.lam (caseL (.bvar 0) [.unreach, .split (.bvar 0) (.bvar 1)]))

theorem meas_head (κ : KEnv) : topVC κ [] headE headTy lenEnv := by
  simp [topVC, headE, headTy, lenEnv, lenListDecl, listDecl]
  intro γ; omega

/-- Without the precondition, `head` is rejected: nothing rules out `Nil`. -/
theorem meas_head_bad (κ : KEnv) :
    ¬ topVC κ [] headE (.forall .star (.arrow (ListT (Par 0)) (Par 0))) lenEnv := by
  simp [topVC, headE, lenEnv, lenListDecl, listDecl]
  exact ⟨{ map := fun _ => .iconst 0 }, rfl⟩

/-! ## `map` preserves the length -/

abbrev mapLenTy : Ty := .forall .star (.forall .star
  (.arrow (.arrow (Par 1) (Par 0)) (.arrow (ListT (Par 1)) (ListLen (Par 0) (lenB 1)))))

theorem meas_map (κ : KEnv) : topVC κ [] mapE mapLenTy lenEnv := by
  simp [topVC, mapE, mapLenTy, lenEnv, lenListDecl, listDecl]
  intro γ; constructor <;> intros <;> omega

/-! ## Building a list: `[1, 2]` has length 2 (and not 3) -/

/-- `let one = 1; let two = 2; let nil = Nil[Int]; let l = Cons(two, nil); Cons(one, l)` -/
abbrev twoE : Exp :=
  .letin (.iconst 1) (.letin (.iconst 2)              -- two=0 one=1
  (.letin (nilE TT)                                   -- nil
  (.letin (consE TT (.bvar 1) (.bvar 0))              -- l = Cons(two, nil)
  (consE TT (.bvar 3) (.bvar 0)))))                   -- Cons(one, l)

theorem meas_two (κ : KEnv) : topVC κ [] twoE (ListLen TT (.const .int 2)) lenEnv := by
  simp [topVC, twoE, lenEnv, lenListDecl, listDecl]
  intro γ; omega

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

theorem meas_headClient_vc (κ : KEnv) : topVC κ [] headClientE TT lenEnv := by
  simp [topVC, headClientE, headE, headTy, lenEnv, lenListDecl, listDecl]
  intro γ _ _ _; constructor <;> intros <;> omega

/-- Running the client never gets stuck — in particular `head` never takes its
    `Nil` branch, which `len` rules out — and any value it returns is an
    integer. -/
theorem meas_headClient_safe (n : Nat) :
    ∃ o, Run n headClientE o ∧ ∀ v m, o = .val v m → ∃ i : Int, v = .iconst i := by
  have hh := topVC_decl_sound (fun _ _ => True) headClientE TT
    (by simp [Exp.WFBVars, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar,
              Term.hasBVar])
    (by simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar])
    (meas_headClient_vc _)
  obtain ⟨o, hrun, hres⟩ := type_safety lenEnv_wf hh n
  refine ⟨o, hrun, fun v m ho => ?_⟩
  have := hres v m ho
  simp only [TyDenote, BaseDen] at this
  obtain ⟨⟨i, rfl⟩, _⟩ := this
  exact ⟨i, rfl⟩

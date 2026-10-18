import Flex.VCG.STLC.MeasureExamples

open STLC

/-! # Inferring measure specifications with Flex

  The specifications of the recursive functions in `MeasureExamples` are left
  as κ-templates over measures (`k(len ν, len xs)`, …) and inferred from what a
  client needs. Each κ sits on a recursive function, so it is *cyclic*: `fix`
  (certifying predicate abstraction, `pa_cert`) finds the strongest
  conjunction of `@[qualif]` instances that is inductive, certifies every
  κ-head in the kernel, and `grind` closes the κ-free residual. Measures are
  plain integer atoms to the solver. A false client — `append` returning
  `len xs` elements — leaves an unprovable residual. -/

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

/-- `len` of BVar i, as a κ argument. -/
abbrev lenA (i : Nat) : (Σ b : Base, Term b) := ⟨.int, lenB i⟩

/-! ## `length`: `xs:list α → Int{k(ν, len xs)}`, solved by `k(ν, n) := ν = n` -/
abbrev lengthTyK : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.refine .int (.kapp "k" [⟨.int, .bvar .int 0⟩, lenA 1])))

theorem infer_length : ∃ κ : KEnv, Check lenEnv κ []
    (.letin (.ann lengthE lengthTyK)
      (.lam (.app (.tapp (.bvar 1) TT) (.bvar 0))))
    (.arrow (ListT TT) (.refine .int (.fmla (.eq .int (.bvar .int 0) (lenB 1))))) := by
  simp only [lengthE, lenEnv, lenListDecl, listDecl]
  generate
  fix

/-! ## `map`: a κ in a datatype refinement, `list β{k(len ν, len xs)}` -/
abbrev mapTyK : Ty := .forall .star (.forall .star
  (.arrow (.arrow (Par 1) (Par 0)) (.arrow (ListT (Par 1))
    (.dataL "list" [Par 0] (.kapp "k" [lenA 0, lenA 1])))))

theorem infer_map : ∃ κ : KEnv, Check lenEnv κ []
    (.letin (.ann mapE mapTyK)
      (.lam (.lam (.app (.app (.tapp (.tapp (.bvar 2) TT) TT) (.bvar 1)) (.bvar 0)))))
    (.arrow (.arrow TT TT) (.arrow (ListT TT) (ListLen TT (lenB 1)))) := by
  simp only [mapE, lenEnv, lenListDecl, listDecl]
  generate
  fix

/-! ## `append`: a three-way relation, `k(len ν, len xs, len ys) := len ν = len xs + len ys` -/
abbrev appendTyK : Ty := .forall .star (.arrow (ListT (Par 0)) (.arrow (ListT (Par 0))
  (.dataL "list" [Par 0] (.kapp "k" [lenA 0, lenA 2, lenA 1]))))

theorem infer_append : ∃ κ : KEnv, Check lenEnv κ []
    (.letin (.ann appendE appendTyK)
      (.lam (.lam (.app (.app (.tapp (.bvar 2) TT) (.bvar 1)) (.bvar 0)))))
    (.arrow (ListT TT) (.arrow (ListT TT) (ListLen TT (.add (lenB 2) (lenB 1))))) := by
  simp only [appendE, lenEnv, lenListDecl, listDecl]
  generate
  fix

/-! ## The statement of a lemma: `nonneg : xs:list α → Int{k(len xs)}`

  The client `cons` calls `nonneg t` and needs `0 < len (Cons h t)`; the solver
  infers the lemma `k(n) := 0 ≤ n`, and the recursion checks it. -/
abbrev nonnegTyK : Ty :=
  .forall .star (.arrow (ListT (Par 0)) (.refine .int (.kapp "k" [lenA 1])))

theorem infer_nonneg : ∃ κ : KEnv, Check lenEnv κ []
    (.letin (.ann nonnegE nonnegTyK)
      (.tabs .star (.lam (.lam                                          -- t=0 h=1 nonneg=2
        (.letin (.app (.tapp (.bvar 2) (Par 0)) (.bvar 0))
          (consE (Par 0) (.bvar 2) (.bvar 1)))))))
    consPosTy := by
  simp only [nonnegE, consPosTy, lenEnv, lenListDecl, listDecl]
  generate
  fix

/-! ## `mirror`: an inferred height relation (the verification condition contains `ite`) -/
abbrev heightA (i : Nat) : (Σ b : Base, Term b) := ⟨.int, heightB i⟩
abbrev mirrorTyK : Ty := .forall .star (.arrow (TreeT (Par 0))
  (TreeT (Par 0) (.kapp "k" [heightA 0, heightA 1])))

theorem infer_mirror : ∃ κ : KEnv, Check htreeEnv κ []
    (.letin (.ann mirrorE mirrorTyK)
      (.lam (.app (.tapp (.bvar 1) TT) (.bvar 0))))
    (.arrow (TreeT TT) (TreeT TT (.fmla (.eq .int (heightB 0) (heightB 1))))) := by
  simp only [mirrorE, htreeEnv, htreeDecl, treeDecl]
  generate
  fix

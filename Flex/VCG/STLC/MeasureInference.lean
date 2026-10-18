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

/-! ## `length`: `xs:list α → Int{k(ν, len xs)}`, where the client needs `ν = len xs` -/
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

/-! ## `append`: a three-way relation `k(len ν, len xs, len ys)`; the client needs `len ν = len xs + len ys` -/
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

  The client `cons` calls `nonneg t` and needs `0 < len (Cons h t)`, i.e. a
  lemma at least as strong as `0 ≤ len t`; the solver finds one that the
  recursion establishes. -/
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

/-! ## `filterGe`: the length bound inferred, alongside the element refinement's κ (`solve` = `zap`, then `fix`) -/
abbrev filterGeTyK : Ty :=
  .arrow TT (.arrow (ListT TT)
    (.dataL "list" [.refine .int (.fmla (.leqI (.bvar .int 2) (.bvar .int 0)))]
      (.kapp "kl" [lenA 0, lenA 1])))

theorem infer_filterGe : ∃ κ : KEnv, Check lenEnv κ []
    (.letin (.ann filterGeE filterGeTyK) (.lam (.lam (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))
    (.arrow TT (.arrow (ListT TT)
      (.dataL "list" [.refine .int (.fmla (.leqI (.bvar .int 2) (.bvar .int 0)))]
        (.fmla (.leqI (lenB 0) (lenB 1)))))) := by
  simp only [filterGeE, lenEnv, lenListDecl, listDecl]
  generate
  solve

/-! ## `sum` over an integer list (an `Int`-field measure) -/
abbrev sumB (i : Nat) : (Σ b : Base, Term b) := ⟨.int, .mbvar "sum" i⟩
theorem infer_sum : ∃ κ : KEnv, Check ilistEnv κ []
    (.letin (.ann sumIListE (.arrow (.dataL "ilist" []) (.refine .int (.kapp "k" [⟨.int, .bvar .int 0⟩, sumB 1]))))
      (.lam (.app (.bvar 1) (.bvar 0))))
    sumIListTy := by
  simp only [sumIListE, ilistEnv, ilistDecl]
  generate
  fix

/-! ## `count` over a list of booleans (a `Bool`-field measure; `ite` in the VC) -/
theorem infer_count : ∃ κ : KEnv, Check blistEnv κ []
    (.letin (.ann countE (.arrow (.dataL "blist" [])
        (.refine .int (.kapp "k" [⟨.int, .bvar .int 0⟩, ⟨.int, countB 1⟩]))))
      (.lam (.app (.bvar 1) (.bvar 0))))
    countTy := by
  simp only [countE, blistEnv, blistDecl]
  generate
  fix

/-! ## `node`, with the statement of its size lemma inferred -/
abbrev sizeA (i : Nat) : (Σ b : Base, Term b) := ⟨.int, sizeB i⟩
theorem infer_node : ∃ κ : KEnv, Check treeEnv κ []
    (.letin (.ann sizeNonnegE (.forall .star (.arrow (TreeT (Par 0)) (.refine .int (.kapp "k" [sizeA 1])))))
      (.tabs .star (.lam (.lam (.lam                                   -- r=0 x=1 l=2 lemma=3
        (.letin (.app (.tapp (.bvar 3) (Par 0)) (.bvar 0))
          (.ctor "tree" 1 [Par 0] (.pair (.bvar 3) (.pair (.bvar 2) (.bvar 1))))))))))
    nodeTy := by
  simp only [sizeNonnegE, nodeTy, treeEnv, treeDecl]
  generate
  fix

/-! ## A lemma relating two measures, inferred: the client needs `height t ≤ size t`; the
  induction also needs `0 ≤ height t` (and `0 ≤ size t`), which the solver finds too -/
theorem infer_heightLeSize : ∃ κ : KEnv, Check htreeEnv κ []
    (.letin (.ann sizeNonnegE (.forall .star (.arrow (TreeT (Par 0))
        (.refine .int (.kapp "k" [heightA 1, sizeA 1])))))
      (.lam (.app (.tapp (.bvar 1) TT) (.bvar 0))))
    (.arrow (TreeT TT) (.refine .int (.fmla (.leqI (heightB 1) (sizeB 1))))) := by
  simp only [sizeNonnegE, htreeEnv, htreeDecl, treeDecl]
  generate
  fix

/-! ## Ordered-list `insert` (polymorphic recursion), adding one element -/

@[qualif] def QSuccM (a b : Int) : Prop := a = b + 1

abbrev insTyK : Ty := .forall .B (.arrow (Par 0) (.arrow (OListT (Par 0))
  (.dataL "olist" [Par 0] (.kapp "k" [lenA 0, lenA 1]))))

theorem infer_insert : ∃ κ : KEnv, Check olistLenEnv κ []
    (.letin (.ann insE insTyK)
      (.lam (.lam (.app (.app (.tapp (.bvar 2) TT) (.bvar 1)) (.bvar 0)))))
    (.arrow TT (.arrow (OListT TT)
      (.dataL "olist" [TT] (.fmla (.eq .int (lenB 0) (.add (.const .int 1) (lenB 1))))))) := by
  simp only [insE, olistLenEnv, olistDecl]
  generate
  solve

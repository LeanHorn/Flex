import Flex.VCG.STLC.Examples.MeasureInference

open STLC

/-! # The earlier examples, through Flex

  Programs of `Examples`, `DataExamples` and `OrdExamples` proved there via
  `topVC`, restated as `∃ κ, Check …` and proved by `generate; solve`. Some VCs
  are already closed by `generate`, hence `all_goals`. -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var DataDecl.measBody? Base.constSubst
  TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons caseL

theorem flex_loopMain_vc : ∃ κ : KEnv, Check [] κ [] loopMain <ty| Int{ν : ⊥} |> := by
  simp only [check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        loopMain, loop, loopTy, self, prim, Refinement.interp, Formula.interp, Term.interp,
        REnv.get, TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]
  generate
  all_goals solve

theorem flex_poly_id : ∃ κ : KEnv, Check [] κ [] idPoly idTy := by
  simp only [idPoly, idTy]
  generate
  all_goals solve

theorem flex_poly_choose : ∃ κ : KEnv, Check [] κ [] choosePoly chooseTy := by
  simp only [choosePoly, chooseTy]
  generate
  all_goals solve

theorem flex_poly_impredicative : ∃ κ : KEnv, Check [] κ []
    <| let idF : ⌜idFTy⌝ = ⌜idF⌝ in idF[∀ β : ⋆, β -> β] idF |> idFTy := by
  simp only [idF, idFTy]
  generate
  all_goals solve

theorem flex_poly_iter : ∃ κ : KEnv, Check [] κ [] iterPoly iterTy := by
  simp only [iterPoly, iterTy]
  generate
  all_goals solve

theorem flex_poly_tapp_var : ∃ κ : KEnv, Check [] κ []
    <| λ n, let m = n in (⌜idPoly⌝ : ⌜idTy⌝)[Int{ν : n ≤ ν}] m |>
    <ty| (n : Int) -> Int{ν : n ≤ ν} |> := by
  simp only [idPoly, idTy]
  generate
  all_goals solve

theorem flex_poly_nest : ∃ κ : KEnv, Check [] κ [] nestE nestTy := by
  generate
  all_goals solve

theorem flex_data_fromSome : ∃ κ : KEnv, Check optionEnv κ [] fromSomeE fromSomeTy := by
  simp only [fromSomeE, fromSomeTy, optionEnv, optionDecl]
  generate
  all_goals solve

theorem flex_data_ordOK : ∃ κ : KEnv, Check ordEnv κ [] ordOKE <ty| ⌜OrdT⌝ -> ⌜TrueB⌝ |> := by
  simp only [ordOKE, ordEnv, ordDecl]
  generate
  all_goals solve

theorem flex_data_mkOrd : ∃ κ : KEnv, Check ordEnv κ []
    <| let a = 3 in let b = 5 in MkOrd a b |> OrdT := by
  simp only [ordEnv, ordDecl]
  generate
  all_goals solve

theorem flex_data_sumList : ∃ κ : KEnv, Check listEnv κ [] sumListE sumListTy := by
  simp only [sumListE, sumListTy, listEnv, listDecl]
  generate
  all_goals solve

theorem flex_data_map : ∃ κ : KEnv, Check listEnv κ [] mapE mapTy := by
  simp only [mapE, mapTy, listEnv, listDecl]
  generate
  all_goals solve

theorem flex_data_sumList_pos : ∃ κ : KEnv, Check listEnv κ []
    <| λ xs, (⌜sumListE⌝ : ⌜sumListTy⌝) xs |> <ty| list[⌜Pos⌝] -> ⌜NatT⌝ |> := by
  simp only [sumListE, sumListTy, listEnv, listDecl]
  generate
  all_goals solve

theorem flex_data_pred_contra : ∃ κ : KEnv, Check predEnv κ [] <| λ p, p |> <ty| pred[Int] -> pred[⌜NatT⌝] |> := by
  simp only [predEnv, predDecl]
  generate
  all_goals solve

theorem flex_data_append : ∃ κ : KEnv, Check listEnv κ [] appendE appendTy := by
  simp only [appendE, appendTy, listEnv, listDecl]
  generate
  all_goals solve

theorem flex_ord_max : ∃ κ : KEnv, Check [] κ [] maxE maxTy := by
  generate
  all_goals solve

theorem flex_ord_max_bool : ∃ κ : KEnv, Check [] κ []
    <| let ff = false in let tt = true in (⌜maxE⌝ : ⌜maxTy⌝)[Bool] ff tt |> TrueB := by
  generate
  all_goals solve

theorem flex_ord_insert : ∃ κ : KEnv, Check olistEnv κ [] insE insTy := by
  simp only [olistEnv, olistDecl]
  generate
  all_goals solve

theorem flex_ord_isort : ∃ κ : KEnv, Check sortEnv κ [] isortE isortTy := by
  simp only [sortEnv, olistDecl, listDecl]
  generate
  all_goals solve

theorem flex_ord_headsOrdered : ∃ κ : KEnv, Check olistEnv κ [] headsOrderedE headsTy := by
  simp only [olistEnv, olistDecl]
  generate
  all_goals solve

theorem flex_ord_sortClient_vc : ∃ κ : KEnv, Check sortEnv κ [] sortClientE TrueB := by
  simp only [sortEnv, olistDecl, listDecl]
  generate
  all_goals solve

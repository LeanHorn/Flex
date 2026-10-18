import Flex.VCG.STLC.MeasureInference

open STLC

/-! # The earlier examples, through Flex

  The programs of `Examples`, `DataExamples` and `OrdExamples` that are proved
  there by computing `topVC` and closing it with `omega`/`grind`/`split_sorts`,
  restated as `∃ κ, Check …` and handed to the Flex pipeline unchanged:
  `generate` computes the verification condition (reifying the κ's, if any —
  these programs have none), and `solve` (`zap`, then `fix`) closes what is
  left. Some VCs are already closed by `generate`'s simplification, hence
  `all_goals`. -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var DataDecl.measBody? Base.constSubst
  TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons caseL

theorem flex_loopMain_vc : ∃ κ : KEnv, Check [] κ [] loopMain (.refine .int (.fmla .ff)) := by
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

theorem flex_poly_impredicative : ∃ κ : KEnv, Check [] κ [] (.letin (.ann idF idFTy) (.app (.tapp (.bvar 0) idFTy) (.bvar 0))) idFTy := by
  simp only [idF, idFTy]
  generate
  all_goals solve

theorem flex_poly_iter : ∃ κ : KEnv, Check [] κ [] iterPoly iterTy := by
  simp only [iterPoly, iterTy]
  generate
  all_goals solve

theorem flex_poly_tapp_var : ∃ κ : KEnv, Check [] κ [] (.lam (.letin (.bvar 0) (.app (.tapp (.ann idPoly idTy) (.refine .int (.fmla (.leqI (.bvar .int 2) (.bvar .int 0))))) (.bvar 0)))) (.arrow TT (.refine .int (.fmla (.leqI (.bvar .int 1) (.bvar .int 0))))) := by
  simp only [idPoly, idTy]
  generate
  all_goals solve

theorem flex_poly_nest : ∃ κ : KEnv, Check [] κ [] (nestE (.app (.tapp (.bvar 7) (.arrow TT (TV ttR))) (.bvar 2))) nestTy := by
  generate
  all_goals solve

theorem flex_data_fromSome : ∃ κ : KEnv, Check optionEnv κ [] fromSomeE fromSomeTy := by
  simp only [fromSomeE, fromSomeTy, optionEnv, optionDecl]
  generate
  all_goals solve

theorem flex_data_ordOK : ∃ κ : KEnv, Check ordEnv κ [] ordOKE (.arrow OrdT TrueB) := by
  simp only [ordOKE, ordEnv, ordDecl]
  generate
  all_goals solve

theorem flex_data_mkOrd : ∃ κ : KEnv, Check ordEnv κ [] (.letin (.iconst 3) (.letin (.iconst 5) (.ctor "ord" 0 [] (.pair (.bvar 1) (.bvar 0))))) OrdT := by
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

theorem flex_data_sumList_pos : ∃ κ : KEnv, Check listEnv κ [] (.lam (.app (.ann sumListE sumListTy) (.bvar 0))) (.arrow (ListT Pos) NatT) := by
  simp only [sumListE, sumListTy, listEnv, listDecl]
  generate
  all_goals solve

theorem flex_data_pred_contra : ∃ κ : KEnv, Check predEnv κ [] (.lam (.bvar 0)) (.arrow (.dataL "pred" [TT]) (.dataL "pred" [NatT])) := by
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

theorem flex_ord_max_bool : ∃ κ : KEnv, Check [] κ [] (.letin (.bconst false) (.letin (.bconst true) (.app (.app (.tapp (.ann maxE maxTy) BoolT) (.bvar 1)) (.bvar 0)))) TrueB := by
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

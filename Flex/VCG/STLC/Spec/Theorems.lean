import Flex.VCG.STLC.Proofs.Safety

open STLC

/-! # The headline theorems

  Every theorem here concludes with `Run` (`Spec/Semantics`) and `TyDenote`
  (`Spec/Denotation`): a program never gets stuck, and whatever it returns is in
  its type's denotation. Their hypotheses (`Hastype`, `Check`, `topVC`, `wfB`,
  `WFBVars`) are defined in `Checker/` and need not be trusted, only shown
  satisfiable — which the end-to-end examples do. The proofs are short
  compositions of the fundamental lemma (`Proofs/Safety`) and the soundness of
  the checker (`Proofs/Soundness`); this is the one `Spec` file that imports
  proofs. -/


/-- A well-typed closed program never gets stuck: for every fuel budget `n` it
    either times out or returns a value, and every returned value (with `m`
    fuel left) is in its type's denotation at index `m`. -/
theorem type_safety {de : DEnv} {κ : KEnv} {e : Exp} {t : Ty} (hde : de.wfB = true)
    (h : Hastype de κ [] e t) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ (TyEnvSem.empty de) m t REnv.empty v := by
  intro n
  have hfv : e.fv = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
      obtain ⟨t', ht'⟩ := h.fv_subset z hz; simp at ht'
  have hden := hastype_fundamental hde h (TyEnvSem.empty_WK de) rfl (k := n) (γ := REnv.empty)
    (by simp [EnvCloses])
  rw [Exp.substEnv_closed REnv.empty e hfv] at hden
  exact hden

/-- A closed program accepted by the bidirectional checker is safe. -/
theorem check_safety {de : DEnv} {κ : KEnv} {e : Exp} {t : Ty} (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : Check de κ [] e t) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ (TyEnvSem.empty de) m t REnv.empty v :=
  type_safety hde (check_to_hastype TEnv.WFBVars.empty hE ht h)

/-- A closed program whose verification condition holds is safe. -/
theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty} {de : DEnv} (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t de) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ (TyEnvSem.empty de) m t REnv.empty v :=
  type_safety hde (topVC_decl_sound κ e t hE ht h)

/-- Progress: a program accepted by VCGen never gets stuck. -/
theorem vcgen_no_stuck {κ : KEnv} {e : Exp} {t : Ty} {de : DEnv} (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t de) :
    ∀ n, ∃ o, Run n e o := fun n =>
  let ⟨o, hev, _⟩ := vcgen_safety hde hE ht h n
  ⟨o, hev⟩

/-- Partial correctness at base type: if a program accepted by VCGen terminates
    (under any fuel budget), its value has the result sort and satisfies the
    result refinement. -/
theorem vcgen_partial_correct {κ : KEnv} {e : Exp} {b : Base} {r : Refinement} {de : DEnv}
    (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars (.refine b r)) (h : topVC κ [] e (.refine b r) de)
    {n m : Nat} {v : Val} (hev : Run n e (.val v m)) :
    BaseDen (TyEnvSem.empty de) m b v ∧
      Refinement.interp κ r ({ REnv.empty with sorts := { meas := de.measEval } }.push v) := by
  obtain ⟨o, hev', hres⟩ := vcgen_safety hde hE ht h n
  cases Eval.det hev hev'
  have e : REnv.empty.withSorts (TyEnvSem.empty de).sorts =
      { REnv.empty with sorts := { meas := de.measEval } } := by
    apply REnv.ext <;> try rfl
    simp only [REnv.empty, TyEnvSem.sorts, TyEnvSem.empty]
    congr 1
    funext a
    rcases a with ⟨_, _ | _⟩ <;> rfl
  have := hres v m rfl
  simp only [TyDenote, e] at this
  exact this

/-! ## Axioms -/

/-- info: 'type_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms type_safety

/-- info: 'check_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_safety

/-- info: 'vcgen_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vcgen_safety

/-- info: 'vcgen_no_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vcgen_no_stuck

/-- info: 'vcgen_partial_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vcgen_partial_correct

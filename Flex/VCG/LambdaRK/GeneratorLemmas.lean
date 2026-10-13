import Flex.VCG.LambdaRK.VCGen

/-! Success inversion for the state-and-error computation used by the generator.
These lemmas expose successful subcomputations without unfolding their code. -/
namespace LambdaRK

namespace GenM

theorem bind_ok {action : GenM α} {next : α → GenM β} {state final : Nat} {value : β} :
    (action >>= next) state = .ok (value, final) ↔
      ∃ intermediate middle, action state = .ok (intermediate, middle) ∧
        next intermediate middle = .ok (value, final) := by
  change (Except.bind (action state) (fun (a,s) => next a s) = _) ↔ _
  cases h : action state with
  | error e => simp [Except.bind]
  | ok pair => cases pair; simp [Except.bind]; grind

theorem lift_ok {action : Except String α} {state final : Nat} {value : α} :
    (liftM action : GenM α) state = .ok (value, final) ↔
      action = .ok value ∧ state = final := by
  change (Except.bind action (fun a => .ok (a,state)) = _) ↔ _
  cases action <;> simp [Except.bind, Prod.mk.injEq]

theorem pure_ok {state final : Nat} {left right : α} :
    (pure left : GenM α) state = .ok (right, final) ↔ left = right ∧ state = final := by
  change Except.ok (left,state) = Except.ok (right,final) ↔ _
  simp

theorem throw_not_ok {state : Nat} {result : α × Nat} {message : String} :
    (throw message : GenM α) state ≠ .ok result := by
  intro h
  cases h

theorem run'_ok {action : GenM α} {state : Nat} {value : α} :
    action.run' state = .ok value ↔ ∃ final, action state = .ok (value, final) := by
  change Except.map Prod.fst (action state) = .ok value ↔ _
  cases h : action state with
  | error message => simp [Except.map]
  | ok pair => cases pair; simp [Except.map]

end GenM

theorem except_bind_ok {action : Except String α} {next : α → Except String β} {value : β} :
    (action >>= next) = .ok value ↔ ∃ intermediate,
      action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action <;> simp [bind, Except.bind]

@[simp] theorem checkScope_ok {context : Context} {type : Ty} :
    checkScope context type = .ok () ↔ type.InScope context := by
  simp [checkScope, failUnless, Ty.scopeCheck_eq_true]

theorem finishSynth_ok {context : Context} {output result : Cstr × Ty} {state final : Nat} :
    finishSynth context output state = .ok (result, final) ↔
      output = result ∧ state = final ∧ output.2.InScope context := by
  unfold finishSynth
  rw [GenM.bind_ok]
  simp only [GenM.lift_ok, GenM.pure_ok]
  constructor
  · rintro ⟨u, middle, ⟨hasScope, rfl⟩, same, rfl⟩
    cases u
    exact ⟨same, rfl, checkScope_ok.mp hasScope⟩
  · rintro ⟨rfl, rfl, hasScope⟩
    exact ⟨(), state, ⟨checkScope_ok.mpr hasScope, rfl⟩, rfl, rfl⟩

theorem observeFresh_ok {expression : Expr} {observed : LTerm} :
    observeFresh expression = .ok observed ↔
      observe expression = .ok observed ∧ valueName ∉ observed.freeVars := by
  unfold observeFresh
  cases h : observe expression with
  | error message => simp [bind, Except.bind]
  | ok value =>
    by_cases fresh : valueName ∈ value.freeVars
    · simp [bind, Except.bind, failUnless, fresh]
      intro same
      exact same ▸ fresh
    · simp [bind, Except.bind, failUnless, fresh, pure, Except.pure]
      intro same
      exact same ▸ fresh

end LambdaRK

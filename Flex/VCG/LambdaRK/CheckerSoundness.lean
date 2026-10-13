import Flex.VCG.LambdaRK.GeneratorSynthesis
import Flex.VCG.LambdaRK.GeneratorChecking

/-! Soundness of executable synthesis, checking, and closed constraint generation.
The mutually recursive computations are justified together by induction on fuel.
Their conclusions use the independent declarative typing rules. -/
namespace LambdaRK

theorem generator_sound (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (fuel : Nat) : SynthSound signature model assignment fuel ∧
      CheckSound signature model assignment fuel := by
  induction fuel with
  | zero =>
    constructor
    · intro context assumptions expression state final constraint type generated _
      rw [synthFuel] at generated
      contradiction
    · intro context assumptions expression state final constraint type generated _
      rw [checkFuel] at generated
      contradiction
  | succ fuel ih =>
    exact ⟨synthFuel_succ_sound ih.1 ih.2, checkFuel_succ_sound ih.1 ih.2⟩

theorem synth_soundness
    (generated : synth signature context expression = .ok (constraint, type))
    (satisfied : Entails signature model assignment context assumptions constraint) :
    HasType signature model assignment context assumptions expression type ∧ type.InScope context := by
  obtain ⟨final, generatedRun⟩ := GenM.run'_ok.mp generated
  exact (generator_sound signature model assignment 1024).1
    context assumptions expression 0 final constraint type generatedRun satisfied

theorem check_soundness
    (generated : check signature context expression type = .ok constraint)
    (satisfied : Entails signature model assignment context assumptions constraint) :
    HasType signature model assignment context assumptions expression type := by
  unfold check at generated
  obtain ⟨u, _, checked⟩ := except_bind_ok.mp generated
  obtain ⟨final, generatedRun⟩ := GenM.run'_ok.mp checked
  exact (generator_sound signature model assignment 1024).2
    context assumptions expression 0 final constraint type generatedRun satisfied

/-- Successful generation records validation and actual checker success. -/
theorem generate_checked
    (generated : generate signature expression type = .ok constraint) :
    signature.validate = .ok () ∧ check signature {} expression type = .ok constraint := by
  unfold generate at generated
  obtain ⟨u, validated, rest⟩ := except_bind_ok.mp generated
  cases u
  obtain ⟨_, _, checked⟩ := except_bind_ok.mp rest
  exact ⟨validated, checked⟩

/-- CHC validity reconstructs a derivation in the independent typing system.
The theorem does not assume datatype adequacy; adequacy is used later to give
the reconstructed derivation its total-correctness interpretation. -/
theorem checker_soundness (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr)
    (generated : generate signature expression type = .ok constraint)
    (satisfied : constraint.Valid signature assignment) :
    HasType signature model assignment {} [] expression type :=
  check_soundness (generate_checked generated).2 (Entails.of_valid satisfied)

end LambdaRK

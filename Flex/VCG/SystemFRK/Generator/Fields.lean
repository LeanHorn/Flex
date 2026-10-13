import Flex.VCG.SystemFRK.Generator.Monad
import Flex.VCG.SystemFRK.Generator.Constraints

/-! Structural correctness of constructor-field traversal. -/
namespace SystemFRK

/-- Successful traversal exposes a declaratively typed field telescope when
its per-field checker is sound. -/
theorem checkFieldsWith_sound
    (checkField : Expr → Ty → GenM Cstr)
    (fieldSound : ∀ field type constraint start finish,
      checkField field type start = .ok (constraint, finish) →
      Entails signature model assignment context assumptions constraint →
      HasType signature model assignment context assumptions field type)
    (fields : List Expr) (types : List Ty) (constraint : Cstr) (start finish : Nat)
    (generated : checkFieldsWith checkField fields types start = .ok (constraint, finish))
    (satisfied : Entails signature model assignment context assumptions constraint) :
    HasTypes signature model assignment context assumptions fields types := by
  induction fields generalizing types constraint start finish with
  | nil =>
    cases types with
    | nil => exact .nil
    | cons type types => exact False.elim (GenM.throw_not_ok generated)
  | cons field fields ih =>
    cases types with
    | nil => exact False.elim (GenM.throw_not_ok generated)
    | cons type types =>
      rw [checkFieldsWith] at generated
      obtain ⟨head, middle, headGenerated, rest⟩ := GenM.bind_ok.mp generated
      obtain ⟨tail, final, tailGenerated, result⟩ := GenM.bind_ok.mp rest
      obtain ⟨rfl, rfl⟩ := GenM.pure_ok.mp result
      obtain ⟨headValid, tailValid⟩ := (Entails.andThen head tail).mp satisfied
      exact .cons (fieldSound field type head start middle headGenerated headValid)
        (ih types tail middle final tailGenerated tailValid)

theorem except_forM_ok {α : Type} (entries : List α) (action : α → Except String PUnit)
    (successful : entries.forM action = .ok PUnit.unit) :
    ∀ entry ∈ entries, action entry = .ok PUnit.unit := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    rw [List.forM] at successful
    cases head : action entry with
    | error message => simp [head, bind, Except.bind] at successful
    | ok result =>
      cases result
      simp only [head, bind, Except.bind] at successful
      intro selected member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact ih successful selected member

theorem arguments_forM_formed (signature : Signature) (context : Context) (arguments : List Ty)
    (successful : (arguments.forM (fun argument => do
      wfTy signature context 512 argument
      pure PUnit.unit) : Except String PUnit) = .ok PUnit.unit) :
    ∀ argument ∈ arguments, wfTy signature context 512 argument = .ok () := by
  intro argument member
  have checked := except_forM_ok arguments _ successful argument member
  cases formed : wfTy signature context 512 argument with
  | error message => simp [formed, bind, Except.bind] at checked
  | ok result => cases result; rfl

end SystemFRK

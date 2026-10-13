import Flex.VCG.SystemFRK.Generator.Monad
import Flex.VCG.SystemFRK.Generator.Constraints

/-! Soundness of the structural traversal over checked pattern branches. -/
namespace SystemFRK

theorem checkBranchesWith_sound
    (checkBody : Context → Expr → Ty → GenM Cstr)
    (bodySound : ∀ context assumptions body type start finish constraint,
      checkBody context body type start = .ok (constraint, finish) →
      Entails signature model assignment context assumptions constraint →
      HasType signature model assignment context assumptions body type)
    (context : Context) (assumptions : List Atom) (scrutinee : String)
    (data : DataDecl) (arguments : List Ty) (expected : Ty)
    (branches : List (String × List String × Expr))
    (constraint : Cstr) (start finish : Nat)
    (generated : checkBranchesWith checkBody context scrutinee data arguments expected branches start =
      .ok (constraint, finish))
    (satisfied : Entails signature model assignment context assumptions constraint) :
    BranchesTyped signature model assignment context assumptions scrutinee data arguments branches expected := by
  induction branches generalizing constraint start finish with
  | nil => exact .nil
  | cons branch rest ih =>
    obtain ⟨name, names, body⟩ := branch
    rw [checkBranchesWith] at generated
    cases found : data.ctors.find? (fun ctor => ctor.name == name) with
    | none =>
      simp only [found] at generated
      exact False.elim (GenM.throw_not_ok generated)
    | some constructor =>
      simp only [found] at generated
      obtain ⟨result, first, arity, remainder⟩ := GenM.bind_ok.mp generated
      obtain ⟨arityPure, rfl⟩ := (GenM.lift_ok (action := failUnless
        (names.length == constructor.fields.length) "pattern has the wrong number of fields")).mp arity
      cases result
      have length : names.length = constructor.fields.length := by
        simpa [failUnless] using arityPure
      obtain ⟨next, first, added, remainder⟩ := GenM.bind_ok.mp remainder
      obtain ⟨addedPure, rfl⟩ := (GenM.lift_ok (action := extendFields context
        (names.zip (constructor.fields.map (Ty.instantiateParams arguments))))).mp added
      obtain ⟨bodyC, middle, bodyGenerated, remainder⟩ := GenM.bind_ok.mp remainder
      obtain ⟨restC, final, restGenerated, finished⟩ := GenM.bind_ok.mp remainder
      obtain ⟨rfl, rfl⟩ := GenM.pure_ok.mp finished
      obtain ⟨branchValid, restValid⟩ := (Entails.andThen _ _).mp satisfied
      have ctorMember := List.mem_of_find?_eq_some found
      have ctorName : constructor.name = name := by
        simpa using List.find?_some found
      exact .cons ctorMember ctorName length addedPure
        (bodySound _ _ body expected start middle bodyC bodyGenerated
          (Entails.guard (Entails.markSmaller (Entails.bindFields addedPure branchValid))))
        (ih restC middle final restGenerated restValid)

end SystemFRK

import Flex.VCG.SystemFRK.Generator.Specification
import Flex.VCG.SystemFRK.Generator.Introduction
import Flex.VCG.SystemFRK.Generator.Branches
import Flex.VCG.SystemFRK.Generator.Subtyping

/-! Soundness of bidirectional checking, given the preceding fuel layer. -/
namespace SystemFRK

private theorem eraseDups_length_properties (names : List String) : names.eraseDups.length ≤ names.length ∧
    (names.eraseDups.length = names.length → names.Nodup) := by
  generalize size : names.length = n
  induction n using Nat.strongRecOn generalizing names with
  | ind n ih =>
    cases names with
    | nil => simp
    | cons name names =>
      let rest := names.filter (fun b => !b == name)
      have bounded : rest.length ≤ names.length := List.length_filter_le _ _
      have smaller : rest.length < n := by simp only [List.length_cons] at size; omega
      obtain ⟨lengthBound, noDups⟩ := ih rest.length smaller rest rfl
      rw [List.eraseDups_cons, ← size]
      change rest.eraseDups.length + 1 ≤ names.length + 1 ∧ _
      constructor
      · omega
      · intro equal
        change rest.eraseDups.length + 1 = names.length + 1 at equal
        have eqLength : rest.length = names.length := by omega
        have same : rest = names := (List.filter_sublist (p := fun b => !b == name) (l := names)).eq_of_length eqLength
        have nodup := noDups (by omega)
        rw [same] at nodup
        apply List.nodup_cons.mpr
        refine ⟨?_, nodup⟩
        intro member
        have bad : name ∈ rest := same.symm ▸ member
        simp [rest] at bad

private theorem nodup_of_eraseDups_length (names : List String)
    (same : names.eraseDups.length = names.length) : names.Nodup :=
  (eraseDups_length_properties names).2 same

private theorem checked_fallback
    (synthIH : SynthSound signature model assignment fuel)
    (generated : (do
      let (left, actual) ← synthFuel signature context fuel expression
      let right ← subtype signature context fuel actual expected
      pure (left.andThen right)) start = .ok (constraint, finish))
    (satisfied : Entails signature model assignment context assumptions constraint) :
    HasType signature model assignment context assumptions expression expected := by
  obtain ⟨⟨left, actual⟩, middle, synthesized, rest⟩ := GenM.bind_ok.mp generated
  obtain ⟨right, last, subtyped, finished⟩ := GenM.bind_ok.mp rest
  obtain ⟨rfl, rfl⟩ := GenM.pure_ok.mp finished
  obtain ⟨leftValid, rightValid⟩ := (Entails.andThen _ _).mp satisfied
  exact (synthIH context assumptions expression start middle left actual synthesized leftValid).1.subsumption
    (subtype_entails subtyped rightValid)

theorem checkFuel_succ_sound
    (synthIH : SynthSound signature model assignment fuel)
    (checkIH : CheckSound signature model assignment fuel) :
    CheckSound signature model assignment (fuel + 1) := by
  intro context assumptions expression start finish constraint expected generated satisfied
  rw [checkFuel.eq_def] at generated
  obtain ⟨done, middle, formed, bodyRun⟩ := GenM.bind_ok.mp generated
  obtain ⟨formedPure, rfl⟩ := (GenM.lift_ok (action := checkScope context expected)).mp formed
  cases done
  have expectedScope := checkScope_ok.mp formedPure
  cases expression with
  | lam name domain body =>
    cases base : expected.outerBase <;> simp only [base] at bodyRun
    all_goals try exact checked_fallback synthIH bodyRun satisfied
    case arrow binder targetDomain result =>
      obtain ⟨done, middle, domainFormed, rest⟩ := GenM.bind_ok.mp bodyRun
      obtain ⟨domainFormedPure, rfl⟩ := (GenM.lift_ok (action := wfTy signature context 512 domain)).mp domainFormed
      cases done
      obtain ⟨pre, nextState, preGenerated, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨next, nextState', added, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨addedPure, rfl⟩ := (GenM.lift_ok (action := context.add name domain)).mp added
      obtain ⟨bodyConstraint, last, bodyGenerated, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨done, last', unrefined, finished⟩ := GenM.bind_ok.mp rest
      obtain ⟨unrefinedPure, rfl⟩ := (GenM.lift_ok (action := failUnless expected.outerPredicates.isEmpty
        "annotate a function value before refining it")).mp unrefined
      cases done
      obtain ⟨rfl, rfl⟩ := GenM.pure_ok.mp finished
      obtain ⟨preValid, bodyValid⟩ := (Entails.andThen _ _).mp satisfied
      exact HasType.checked_lam domainFormedPure addedPure expectedScope base
        (by simpa [failUnless] using unrefinedPure) (subtype_entails preGenerated preValid)
        (checkIH next assumptions body nextState last bodyConstraint _ bodyGenerated (Entails.bind addedPure bodyValid))
  | tyLam body =>
    cases base : expected.outerBase <;> simp only [base] at bodyRun
    all_goals try exact checked_fallback synthIH bodyRun satisfied
    case all result =>
      obtain ⟨done, middle, unrefined, bodyGenerated⟩ := GenM.bind_ok.mp bodyRun
      obtain ⟨unrefinedPure, rfl⟩ := (GenM.lift_ok (action := failUnless expected.outerPredicates.isEmpty
        "refined polymorphic introductions need an annotation")).mp unrefined
      cases done
      exact HasType.checked_tyLam base (by simpa [failUnless] using unrefinedPure)
        (checkIH context.underType assumptions body start finish constraint result bodyGenerated satisfied.underType)
  | letE name value body =>
    obtain ⟨⟨left, inferred⟩, middle, synthesized, rest⟩ := GenM.bind_ok.mp bodyRun
    obtain ⟨next, middle', added, rest⟩ := GenM.bind_ok.mp rest
    obtain ⟨addedPure, rfl⟩ := (GenM.lift_ok (action := context.add name inferred)).mp added
    obtain ⟨right, last, bodyGenerated, finished⟩ := GenM.bind_ok.mp rest
    obtain ⟨rfl, rfl⟩ := GenM.pure_ok.mp finished
    obtain ⟨leftValid, rightValid⟩ := (Entails.andThen _ _).mp satisfied
    obtain ⟨valueTyped, valueScope⟩ := synthIH context assumptions value start middle left inferred synthesized leftValid
    exact .letE valueTyped valueScope addedPure
      (fun free => (context.add_eq_ok next name inferred).mp addedPure |>.2.2.1 (expectedScope.2 name free))
      (checkIH next assumptions body middle last right expected bodyGenerated (Entails.bind addedPure rightValid))
  | matchE scrutinee branches =>
    cases scrutinee <;> simp only [] at bodyRun
    all_goals try exact False.elim (GenM.throw_not_ok bodyRun)
    case var scrutineeName =>
      obtain ⟨⟨scrutineeConstraint, scrutineeType⟩, middle, synthesized, rest⟩ := GenM.bind_ok.mp bodyRun
      cases family : scrutineeType.outerBase <;> simp only [family] at rest
      all_goals try exact False.elim (GenM.throw_not_ok rest)
      case data name arguments =>
        cases declared : signature.findData name with
        | none => simp only [declared] at rest; exact False.elim (GenM.throw_not_ok rest)
        | some data =>
          simp only [declared] at rest
          obtain ⟨done, middle', covered, rest⟩ := GenM.bind_ok.mp rest
          obtain ⟨coveredPure, rfl⟩ := (GenM.lift_ok (action := failUnless
            ((branches.map Prod.fst).length == data.ctors.length &&
              (branches.map Prod.fst).eraseDups.length == (branches.map Prod.fst).length &&
              data.ctors.all (fun ctor => (branches.map Prod.fst).contains ctor.name))
            "match must cover every constructor exactly once")).mp covered
          cases done
          obtain ⟨branchesConstraint, last, branchesGenerated, finished⟩ := GenM.bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := GenM.pure_ok.mp finished
          obtain ⟨scrutineeValid, branchesValid⟩ := (Entails.andThen _ _).mp satisfied
          obtain ⟨scrutineeTyped, scrutineeScope⟩ := synthIH context assumptions (.var scrutineeName)
            start middle scrutineeConstraint scrutineeType synthesized scrutineeValid
          have dataScope := Ty.outerBase_inScope scrutineeScope
          rw [family] at dataScope
          have coveredFacts : (branches.map Prod.fst).length = data.ctors.length ∧
              (branches.map Prod.fst).eraseDups.length = (branches.map Prod.fst).length ∧
              ∀ ctor ∈ data.ctors, ctor.name ∈ branches.map Prod.fst := by
            simpa [failUnless, Bool.and_eq_true, List.all_eq_true, and_assoc] using coveredPure
          apply HasType.matchE expectedScope (fun argument member => Ty.data_arguments_inScope dataScope member)
            (by simpa only [family] using scrutineeTyped.outerBase) declared coveredFacts.1
          · exact nodup_of_eraseDups_length _ coveredFacts.2.1
          · exact coveredFacts.2.2
          · exact checkBranchesWith_sound (checkFuel signature · fuel)
              (fun c a e t s f k run valid => checkIH c a e s f k t run valid)
              context assumptions scrutineeName data arguments expected branches branchesConstraint middle last
              branchesGenerated branchesValid
  | _ => exact checked_fallback synthIH bodyRun satisfied

end SystemFRK

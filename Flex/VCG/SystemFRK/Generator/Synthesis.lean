import Flex.VCG.SystemFRK.Generator.Specification
import Flex.VCG.SystemFRK.Generator.Introduction
import Flex.VCG.SystemFRK.Generator.Fields

/-! Synthesis soundness, assuming soundness at the preceding fuel. -/
namespace SystemFRK

theorem synthFuel_succ_sound
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (synthIH : SynthSound signature model assignment fuel)
    (checkIH : CheckSound signature model assignment fuel) :
    SynthSound signature model assignment (fuel+1) := by
  intro context assumptions expression state final constraint type generated satisfied
  cases expression with
  | var name =>
    rw [synthFuel] at generated
    cases lookup : context.vars.lookup name with
    | none => simp only [lookup] at generated; contradiction
    | some ty =>
      simp only [lookup] at generated
      obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp generated
      cases equal
      have scope := wfTy_inScope _ _ _ _ resultFormed
      exact ⟨.var resultFormed lookup, scope⟩
  | int n =>
    rw [synthFuel] at generated
    obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp generated
    cases equal
    have scope := wfTy_inScope _ _ _ _ resultFormed
    exact ⟨.int, scope⟩
  | bool b =>
    rw [synthFuel] at generated
    obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp generated
    cases equal
    have scope := wfTy_inScope _ _ _ _ resultFormed
    exact ⟨.bool, scope⟩
  | ann expression expected =>
    rw [synthFuel] at generated
    obtain ⟨u, middle, formedRun, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨formed, rfl⟩ := GenM.lift_ok.mp formedRun
    cases u
    obtain ⟨bodyC, bodyEnd, bodyGenerated, finish⟩ := GenM.bind_ok.mp rest
    obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
    cases equal
    have scope := wfTy_inScope _ _ _ _ resultFormed
    exact ⟨.ann formed (checkIH _ _ _ _ _ _ _ bodyGenerated satisfied), scope⟩
  | lam name domain body =>
    rw [synthFuel] at generated
    obtain ⟨u, middle, formedRun, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨formed, rfl⟩ := GenM.lift_ok.mp formedRun
    cases u
    obtain ⟨next, middle, addedRun, rest⟩ := GenM.bind_ok.mp rest
    obtain ⟨added, rfl⟩ := GenM.lift_ok.mp addedRun
    obtain ⟨⟨bodyC, codomain⟩, bodyEnd, bodyGenerated, finish⟩ := GenM.bind_ok.mp rest
    obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
    cases equal
    have scope := wfTy_inScope _ _ _ _ resultFormed
    exact ⟨.lam resultFormed formed added (synthIH _ _ _ _ _ _ _ bodyGenerated (Entails.bind validSignature adequate added satisfied)).1, scope⟩
  | tyLam body =>
    rw [synthFuel] at generated
    obtain ⟨⟨bodyC, bodyType⟩, bodyEnd, bodyGenerated, finish⟩ := GenM.bind_ok.mp generated
    obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
    cases equal
    have scope := wfTy_inScope _ _ _ _ resultFormed
    exact ⟨.tyLam resultFormed (synthIH _ _ _ _ _ _ _ bodyGenerated (Entails.underType satisfied)).1, scope⟩
  | tyApp function argument =>
    rw [synthFuel] at generated
    obtain ⟨u, middle, formedRun, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨formed, rfl⟩ := GenM.lift_ok.mp formedRun
    cases u
    obtain ⟨⟨functionC, functionType⟩, functionEnd, functionGenerated, rest⟩ := GenM.bind_ok.mp rest
    cases shape : functionType.outerBase <;> simp only [shape] at rest <;> try contradiction
    case all body =>
      obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp rest
      cases equal
      have scope := wfTy_inScope _ _ _ _ resultFormed
      have functionTyped := (synthIH _ _ _ _ _ _ _ functionGenerated satisfied).1.outerBase
      rw [shape] at functionTyped
      exact ⟨.tyApp resultFormed functionTyped formed, scope⟩
  | app function argument =>
    rw [synthFuel] at generated
    obtain ⟨observation, middle, observedRun, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨observed, rfl⟩ := GenM.lift_ok.mp observedRun
    obtain ⟨observedRaw, witnessFresh⟩ := observeFresh_ok.mp observed
    obtain ⟨⟨functionC, functionType⟩, functionEnd, functionGenerated, rest⟩ := GenM.bind_ok.mp rest
    cases shape : functionType.outerBase <;> simp only [shape] at rest <;> try contradiction
    case arrow binder domain codomain =>
      obtain ⟨argumentC, argumentEnd, argumentGenerated, finish⟩ := GenM.bind_ok.mp rest
      obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
      cases equal
      have scope := wfTy_inScope _ _ _ _ resultFormed
      obtain ⟨functionValid, argumentValid⟩ := (Entails.andThen _ _).mp satisfied
      have functionTyped := (synthIH _ _ _ _ _ _ _ functionGenerated functionValid).1.outerBase
      rw [shape] at functionTyped
      exact ⟨.app resultFormed functionTyped (checkIH _ _ _ _ _ _ _ argumentGenerated argumentValid)
        observedRaw witnessFresh, scope⟩
  | letE name value body =>
    rw [synthFuel] at generated
    obtain ⟨⟨valueC, valueType⟩, valueEnd, valueGenerated, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨next, middle, addedRun, rest⟩ := GenM.bind_ok.mp rest
    obtain ⟨added, rfl⟩ := GenM.lift_ok.mp addedRun
    obtain ⟨⟨bodyC, bodyType⟩, bodyEnd, bodyGenerated, rest⟩ := GenM.bind_ok.mp rest
    obtain ⟨u, middle, freshRun, finish⟩ := GenM.bind_ok.mp rest
    obtain ⟨fresh, rfl⟩ := GenM.lift_ok.mp freshRun
    cases u
    have fresh : name ∉ bodyType.freeVars := by simpa [failUnless] using fresh
    obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
    cases equal
    have scope := wfTy_inScope _ _ _ _ resultFormed
    obtain ⟨valueValid, bodyValid⟩ := (Entails.andThen _ _).mp satisfied
    obtain ⟨valueTyped, valueScope⟩ := synthIH _ _ _ _ _ _ _ valueGenerated valueValid
    exact ⟨.letE resultFormed valueTyped valueScope added fresh
      (synthIH _ _ _ _ _ _ _ bodyGenerated (Entails.bind validSignature adequate added bodyValid)).1, scope⟩
  | ctor name arguments fields =>
    rw [synthFuel] at generated
    cases found : signature.findCtor name with
    | none => simp only [found] at generated; contradiction
    | some pair =>
      obtain ⟨data, ctor⟩ := pair
      simp only [found] at generated
      obtain ⟨u, middle, arityRun, rest⟩ := GenM.bind_ok.mp generated
      obtain ⟨arity, rfl⟩ := GenM.lift_ok.mp arityRun
      cases u
      have length : arguments.length = data.params := by simpa [failUnless] using arity
      obtain ⟨u, middle, argumentsRun, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨argumentsFormed, rfl⟩ := GenM.lift_ok.mp argumentsRun
      cases u
      obtain ⟨u, middle, fieldsArityRun, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨fieldsArity, rfl⟩ := GenM.lift_ok.mp fieldsArityRun
      cases u
      obtain ⟨fieldsC, fieldsEnd, fieldsGenerated, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨observations, middle, observedRun, finish⟩ := GenM.bind_ok.mp rest
      obtain ⟨observed, rfl⟩ := GenM.lift_ok.mp observedRun
      obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
      cases equal
      have scope := wfTy_inScope _ _ _ _ resultFormed
      refine ⟨.ctor resultFormed found length (arguments_forM_formed signature context arguments argumentsFormed) ?_ observed, scope⟩
      exact checkFieldsWith_sound _
        (fun field expected c start finish success valid => checkIH context assumptions field start finish c expected success valid)
        fields _ _ _ _ fieldsGenerated satisfied
  | structRec name domain codomain body =>
    rw [synthFuel] at generated
    obtain ⟨u, middle, formedRun, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨formed, rfl⟩ := GenM.lift_ok.mp formedRun
    cases u
    cases shape : domain.outerBase <;> simp only [shape] at rest <;> try contradiction
    case data family arguments =>
      obtain ⟨next, middle, addedRun, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨added, rfl⟩ := GenM.lift_ok.mp addedRun
      obtain ⟨u, middle, codomainRun, rest⟩ := GenM.bind_ok.mp rest
      obtain ⟨codomainFormed, rfl⟩ := GenM.lift_ok.mp codomainRun
      cases u
      obtain ⟨bodyC, bodyEnd, bodyGenerated, finish⟩ := GenM.bind_ok.mp rest
      obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
      cases equal
      have scope := wfTy_inScope _ _ _ _ resultFormed
      refine ⟨.structRec resultFormed formed shape added codomainFormed ?_, scope⟩
      apply checkIH _ _ _ _ _ _ _ bodyGenerated
      exact (Entails.context_congr (left := next) rfl rfl).mp (Entails.bind validSignature adequate added satisfied)
  | recur argument =>
    rw [synthFuel] at generated
    cases found : context.recursion with
    | none => simp only [found] at generated; contradiction
    | some recursion =>
      simp only [found] at generated
      cases argument <;> try contradiction
      case var name =>
        obtain ⟨u, middle, smallerRun, rest⟩ := GenM.bind_ok.mp generated
        obtain ⟨smaller, rfl⟩ := GenM.lift_ok.mp smallerRun
        cases u
        have member : name ∈ context.smaller := by simpa [failUnless] using smaller
        obtain ⟨argumentC, argumentEnd, argumentGenerated, finish⟩ := GenM.bind_ok.mp rest
        obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
        cases equal
        have scope := wfTy_inScope _ _ _ _ resultFormed
        exact ⟨.recur resultFormed found member (checkIH _ _ _ _ _ _ _ argumentGenerated satisfied), scope⟩
  | measure name argument =>
    rw [synthFuel] at generated
    obtain ⟨observation, middle, observedRun, rest⟩ := GenM.bind_ok.mp generated
    obtain ⟨observed, rfl⟩ := GenM.lift_ok.mp observedRun
    obtain ⟨⟨argumentC, argumentType⟩, argumentEnd, argumentGenerated, rest⟩ := GenM.bind_ok.mp rest
    cases found : signature.findMeasure name with
    | none => simp only [found] at rest; contradiction
    | some declaration =>
      simp only [found] at rest
      cases shape : argumentType.outerBase <;> simp only [shape] at rest <;> try contradiction
      case data family arguments =>
        obtain ⟨u, middle, familyRun, finish⟩ := GenM.bind_ok.mp rest
        obtain ⟨familyChecked, rfl⟩ := GenM.lift_ok.mp familyRun
        cases u
        have familyEq : family = declaration.datatype := by simpa [failUnless] using familyChecked
        obtain ⟨equal, _, resultFormed⟩ := finishSynth_ok.mp finish
        cases equal
        have scope := wfTy_inScope _ _ _ _ resultFormed
        have argumentTyped := (synthIH _ _ _ _ _ _ _ argumentGenerated satisfied).1.outerBase
        rw [shape] at argumentTyped
        exact ⟨.measure resultFormed found familyEq.symm argumentTyped observed, scope⟩
  | matchE scrutinee branches =>
    rw [synthFuel] at generated
    contradiction

end SystemFRK

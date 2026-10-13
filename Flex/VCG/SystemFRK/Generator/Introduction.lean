import Flex.VCG.SystemFRK.Generator.Constraints
import Flex.VCG.SystemFRK.Binding.Formation

/-! Declarative introduction rules for bidirectional checking. -/
namespace SystemFRK

theorem HasType.outerBase
    (typed : HasType signature model assignment context assumptions expression type) :
    HasType signature model assignment context assumptions expression type.outerBase := by
  apply typed.subsumption
  intro types environment depth variables facts value valueTyped
  exact type.denote_outer.mp valueTyped |>.1

theorem HasType.of_outerBase
    (typed : HasType signature model assignment context assumptions expression type.outerBase)
    (unrefined : type.outerPredicates.isEmpty = true) :
    HasType signature model assignment context assumptions expression type := by
  apply typed.subsumption
  intro types environment depth variables facts value valueTyped
  apply type.denote_outer.mpr
  exact ⟨valueTyped, by simp [List.isEmpty_iff.mp unrefined]⟩

/-- Function checking combines domain contravariance with capture-avoiding binder renaming. -/
theorem HasType.checked_lam
    (domainFormed : wfTy signature context 512 domain = .ok ())
    (added : context.add name domain = .ok next)
    (expectedScope : expected.InScope context)
    (expectedArrow : expected.outerBase = .arrow binder targetDomain result)
    (unrefined : expected.outerPredicates.isEmpty = true)
    (domainSubtype : Subtype signature model assignment context assumptions targetDomain domain)
    (bodyTyped : HasType signature model assignment next assumptions body
      (Ty.substTerm binder (.var name) result)) :
    HasType signature model assignment context assumptions (.lam name domain body) expected := by
  apply HasType.of_outerBase (type := expected) _ unrefined
  rw [expectedArrow]
  apply (HasType.lam domainFormed added bodyTyped).subsumption
  obtain ⟨_, reserved, fresh, _⟩ := (context.add_eq_ok next name domain).mp added
  have nameFresh : valueName ∉ (LTerm.var name).freeVars := by
    simp only [LTerm.freeVars, List.mem_singleton]
    intro equal
    subst name
    have starts : valueName.startsWith "$" = true := by decide +kernel
    simp [starts] at reserved
  have arrowScope := Ty.outerBase_inScope expectedScope
  rw [expectedArrow] at arrowScope
  intro types environment depth variables facts function functionTyped
  simp only [Ty.denote] at functionTyped ⊢
  intro argument argumentTyped
  obtain ⟨value, application, valueTyped⟩ := functionTyped argument
    (domainSubtype types environment depth variables facts argument argumentTyped)
  refine ⟨value, application, ?_⟩
  rw [result.substTerm_denote signature model assignment types (environment.bind name argument)
    binder (.var name) argument nameFresh (.var (by simp [Environment.bind]))] at valueTyped
  rw [result.environment_congr signature model assignment types
    ((environment.bind name argument).bind binder argument)
    (environment.bind binder argument) ?_] at valueTyped
  · exact valueTyped
  · intro variableName free
    by_cases same : variableName = binder
    · subst variableName; simp [Environment.bind]
    · have member : variableName ∈ context.names := arrowScope.2 variableName
        (by simp [Ty.freeVars, free, same])
      have distinct : variableName ≠ name := fun equal => fresh (equal ▸ member)
      simp [Environment.bind, List.lookup_cons,
        show (variableName == binder) = false from by simpa using same,
        show (variableName == name) = false from by simpa using distinct]

/-- A checked polymorphic introduction has no outer refinement to establish. -/
theorem HasType.checked_tyLam
    (expectedAll : expected.outerBase = .all result)
    (unrefined : expected.outerPredicates.isEmpty = true)
    (bodyTyped : HasType signature model assignment context.underType assumptions body result) :
    HasType signature model assignment context assumptions (.tyLam body) expected := by
  apply HasType.of_outerBase (type := expected) _ unrefined
  rw [expectedAll]
  exact .tyLam bodyTyped

end SystemFRK

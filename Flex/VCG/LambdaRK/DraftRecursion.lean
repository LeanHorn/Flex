import Flex.VCG.LambdaRK.RecursionLemmas
import Flex.VCG.LambdaRK.DraftCore

/-! Declarative structural-recursion cases for the open fundamental theorem.
The well-founded argument is proved in `RecursionLemmas`; these wrappers use
the same formation/substitution interfaces as the System F core. -/
namespace LambdaRK.Draft

theorem semTyped_structRec
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context next : Context} {assumptions : List Atom}
    {name : String} {domain codomain : Ty} {body : Expr}
    (domainFormed : wfTy signature context 512 domain = .ok ())
    (added : context.add name domain = .ok next)
    (codomainFormed : wfTy signature next 512 codomain = .ok ())
    (bodyTyped : SemTyped signature model assignment
      { next with recursion := some { binder := name, domain, codomain }, smaller := [] }
      assumptions body codomain) :
    SemTyped signature model assignment context assumptions (.structRec name domain codomain body)
      (.arrow name domain codomain) := by
  intro hasScope
  have domainScope := wfTy_inScope signature context domain 512 hasScope domainFormed
  have nextScope := scoped_add context next name domain hasScope domainScope added
  have codomainScope := wfTy_inScope signature next codomain 512 nextScope codomainFormed
  exact (semTyped_structRec_of_scope domainScope added codomainScope bodyTyped) hasScope

theorem semTyped_recur
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {scope : RecScope} {name : String}
    (scopeEqual : context.recursion = some scope)
    (smaller : name ∈ context.smaller)
    (argument : SemTyped signature model assignment context assumptions (.var name) scope.domain) :
    SemTyped signature model assignment context assumptions (.recur (.var name))
      (Ty.substTerm scope.binder (.var name) scope.codomain) := by
  intro hasScope facts types environment frame realizes
  obtain ⟨value, result, observed, evaluates, resultTyped⟩ := recursive_call_case
    scopeEqual smaller realizes.recursion (argument hasScope facts types environment frame realizes)
  have nameInScope := hasScope.smaller name smaller
  obtain ⟨⟨entryName, type⟩, member, equal⟩ := List.mem_map.mp nameInScope
  have fresh : name ≠ valueName := by
    simpa only [← equal] using hasScope.witness_fresh member
  refine ⟨result, evaluates, ?_⟩
  exact (type_term_substitution signature model assignment types environment scope.binder
    (.var name) scope.codomain value result (by simpa [LTerm.freeVars] using Ne.symm fresh)
    observed).mpr resultTyped

end LambdaRK.Draft

import Flex.VCG.SystemFRK.Correctness
import Flex.VCG.SystemFRK.Binding.Equality
import Flex.VCG.SystemFRK.Bridge.Flatten
import Flex.VCG.SystemFRK.Bridge.Semantics

/-!
# Frontend and bridge proof audit

Audit every theorem and proposition-valued proof definition in the imported
production SystemFRK development, including private lemmas and the bridge's semantic
normalization and clause assembly. This discovery avoids a stale hand-maintained
list of completed proofs. Every dependency is checked transitively; only Lean's
propositional extensionality, choice, and quotient soundness are permitted.

The typed interfaces below additionally guard the assumptions and conclusions of
the main correctness chain. An axiom audit alone cannot detect a theorem weakened
by adding a premise. The actual solver-generated proof is separately audited in
`SolvedMap`; this module runs without an external solver or demo fixtures.
-/
namespace SystemFRK.ProofAudit

/-! Exact interfaces: generation implies independent declarative typing, typing
implies termination, and the constructed datatype model removes any model premise
from the final source theorem. -/
example : ∀ (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr),
    generate signature expression type = .ok constraint →
    constraint.Valid signature assignment →
    HasType signature model assignment {} [] expression type :=
  checker_soundness

example : ∀ (signature : Signature) (model : DataModel) (assignment : KAssignment),
    signature.validate = .ok () → DatatypeAdequate signature model assignment →
    ∀ (context : Context) (assumptions : List Atom) (expression : Expr) (type : Ty),
    HasType signature model assignment context assumptions expression type →
    SemTyped signature model assignment context assumptions expression type :=
  fundamental_open

example : ∀ (signature : Signature) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr),
    generate signature expression type = .ok constraint →
    constraint.Valid signature assignment →
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature (signature.datatypeModel assignment) assignment [] [] value :=
  generated_total_correctness

example : ∀ (signature : Signature) (assignment : KAssignment),
    signature.validate = .ok () →
    DatatypeAdequate signature (signature.datatypeModel assignment) assignment :=
  Signature.datatypeModel_adequate

/-- Measure totality is conditional on the value's datatype interpretation;
quantified runtime values in raw constraints need not satisfy this premise. -/
example : ∀ (signature : Signature) (model : DataModel) (assignment : KAssignment),
    signature.validate = .ok () → DatatypeAdequate signature model assignment →
    ∀ (types : TypeEnvironment) (environment : Environment) (name : String)
      (declaration : MeasureDecl) (arguments : List Ty) (value : Value),
    signature.findMeasure name = some declaration →
    (Ty.data declaration.datatype arguments).denote
      signature model assignment types environment value →
    ∃ result, MeasureEval signature name value result :=
  measure_total

/-! The assembly theorem requires certificates for every original source clause;
it does not assume the correctness of the executable scalar compiler or solver. -/
example : ∀ (signature : Signature) (assignment : KAssignment) (constraint : Cstr),
    Bridge.ClausesValid signature assignment
      ((Bridge.flatten constraint).toList.map Bridge.SourceClause.constraint) →
    constraint.Valid signature assignment :=
  Bridge.flatten_valid_sound

open Lean Meta Elab

private def userName (name : Name) : Name :=
  (privateToUserName? name).getD name

private def productionName (name : Name) : Bool :=
  let name := userName name
  (`SystemFRK).isPrefixOf name && !(`SystemFRK.ProofAudit).isPrefixOf name

/-- Definitions can contain proofs too (for example, `LawfulBEq` instances).
Metaprogram implementations are not logical roots; their checked proof outputs
and the semantic lemmas they use are audited instead. -/
private def logicalRoots : MetaM (Array Name) := do
  let mut roots := #[]
  for (name, info) in (← getEnv).constants.toList do
    if productionName name then
      let logical ← match info with
        | .thmInfo _ | .axiomInfo _ => pure true
        | .defnInfo _ | .opaqueInfo _ =>
            if info.isUnsafe then pure false else isProp info.type
        | _ => pure false
      if logical then roots := roots.push name
  return roots.qsort Name.lt

private def unexpectedAxioms (name : Name) : CoreM (Array Name) := do
  return (← collectAxioms name).filter fun axiomName =>
    axiomName != ``propext && axiomName != ``Classical.choice && axiomName != ``Quot.sound

private def audit (name : Name) : CoreM Unit := do
  let unexpected ← unexpectedAxioms name
  unless unexpected.isEmpty do
    throwError "SystemFRK declaration contains nonstandard axioms: {name}: {unexpected}"

/-! Exercise both discovery and rejection using temporary declarations. They are
removed before this command finishes: the audit exports no test axiom. -/
run_elab do
  withoutModifyingEnv do
    let axiomName := `SystemFRK.AuditFixture.forbidden
    let indirectName := `SystemFRK.AuditFixture.indirect
    addDecl (.axiomDecl {
      name := axiomName, levelParams := [], type := mkConst ``False, isUnsafe := false })
    addDecl (.thmDecl {
      name := indirectName, levelParams := [], type := mkConst ``False,
      value := mkConst axiomName })
    let privateProof := mkPrivateNameCore (← getEnv).mainModule
      `SystemFRK.AuditFixture.privateProof
    addDecl (.defnDecl {
      name := privateProof, levelParams := [], type := mkConst ``False,
      value := mkConst indirectName, hints := .opaque, safety := .safe })
    let roots ← logicalRoots
    unless roots.contains axiomName && roots.contains indirectName &&
        roots.contains privateProof do
      throwError "proof audit regression: discovery missed a logical declaration"
    for name in [axiomName, indirectName, privateProof] do
      unless (← unexpectedAxioms name) == #[axiomName] do
        throwError "proof audit regression: missed direct or transitive axiom dependency"
      let rejected ← try
        audit name
        pure false
      catch _ => pure true
      unless rejected do
        throwError "proof audit regression: nonstandard axiom was accepted"
    audit ``Nat.add_comm
  if (← getEnv).contains `SystemFRK.AuditFixture.forbidden then
    throwError "proof audit regression: temporary axiom escaped the test environment"

run_elab do
  let environment ← getEnv
  for moduleName in environment.header.moduleNames do
    if moduleName.toString.startsWith "Flex.VCG.SystemFRK.Draft" then
      throwError "canonical SystemFRK proof audit still imports a compatibility module: {moduleName}"
  let roots ← logicalRoots
  -- Presence checks catch a narrowed import closure even if all remaining roots
  -- are axiom-free. New lemmas in these modules are discovered automatically.
  for required in [
      ``Ty.freshenBindersAux_scoped, ``LTerm.equal_eq_true,
      ``Signature.datatypeModel_adequate, ``Eval.deterministic,
      ``MeasureEval.deterministic, ``MeasureEval.defining_equation,
      ``measure_total, ``subtype_sound, ``generator_sound,
      ``checker_soundness, ``fundamental_open, ``generated_total_correctness,
      ``Bridge.applyPredicate_int_cons, ``Bridge.logical_measure,
      ``Bridge.measure_ctor, ``Bridge.flatten_sound, ``Bridge.flatten_valid_sound] do
    unless roots.contains required do
      throwError "proof audit is missing a required canonical declaration: {required}"
  let mut bridgeCount : Nat := 0
  let mut privateCount : Nat := 0
  for name in roots do
    audit name
    if (`SystemFRK.Bridge).isPrefixOf (userName name) then bridgeCount := bridgeCount + 1
    if (privateToUserName? name).isSome then privateCount := privateCount + 1
  logInfo m!"SystemFRK proof audit: {roots.size} logical declarations ({bridgeCount} bridge, {privateCount} private) use only standard Lean axioms; correctness interfaces and audit rejection checks passed"

end SystemFRK.ProofAudit

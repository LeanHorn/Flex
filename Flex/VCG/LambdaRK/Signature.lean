import Flex.VCG.LambdaRK.DatatypeSyntax

/-!
# Executable signature validation

Declarations are ordered: datatype fields may refer to earlier datatypes or to
the datatype currently being declared. The first version rejects mutual and
nested recursion. Direct recursive occurrences must be strictly positive and
use the declaration's parameters unchanged. This conservative regular-datatype
fragment includes Option, List, and Tree, without assuming variance information
for arbitrary earlier datatype constructors.
-/

namespace LambdaRK

namespace Signature

def findData (signature : Signature) (name : String) : Option DataDecl :=
  signature.datatypes.find? (·.name == name)

def findCtor (signature : Signature) (name : String) : Option (DataDecl × CtorDecl) :=
  signature.datatypes.findSome? fun datatype =>
    datatype.ctors.findSome? fun ctor =>
      if ctor.name == name then some (datatype, ctor) else none

def findMeasure (signature : Signature) (name : String) : Option MeasureDecl :=
  signature.measures.find? (·.name == name)

def findKVar (signature : Signature) (name : String) : Option KDecl :=
  signature.kvars.find? (·.name == name)

private def uniqueNames (kind : String) (names : List String) : Except String Unit := do
  let mut seen : List String := []
  for name in names do
    if name.isEmpty || name == valueName then
      throw s!"invalid {kind} name '{name}'"
    if seen.contains name then throw s!"duplicate {kind} name '{name}'"
    seen := name :: seen

/-- The depth bound is an implementation guard, not an assumed well-formedness
proof. Exhaustion is rejected and may be overridden by `validate`. -/
private def validateField (earlier : List DataDecl) (current : DataDecl)
    (fuel depth : Nat) (positive : Bool) (ty : Ty) : Except String Unit := do
  match fuel with
  | 0 => throw "datatype field validation exceeded its depth limit"
  | fuel + 1 =>
    match ty with
    | .var index =>
      if index ≥ current.params + depth then
        throw s!"unbound type variable {index} in datatype '{current.name}'"
    | .int | .bool => pure ()
    | .data name args =>
      if name == current.name then
        if !positive then
          throw s!"non-positive or nested recursive occurrence of '{name}'"
        let expected := (List.range current.params).map (fun i => Ty.var (i + depth))
        if args != expected then
          throw s!"recursive datatype '{name}' must preserve its parameters"
      else
        let some decl := earlier.find? (·.name == name)
          | throw s!"unknown or forward datatype reference '{name}'"
        if args.length != decl.params then
          throw s!"datatype '{name}' expects {decl.params} type arguments"
        for arg in args do validateField earlier current fuel depth false arg
    | .arrow binder domain codomain =>
      if binder.isEmpty || binder == valueName then
        throw s!"invalid datatype function-field binder '{binder}'"
      validateField earlier current fuel depth false domain
      validateField earlier current fuel depth positive codomain
    | .all body => validateField earlier current fuel (depth + 1) positive body
    | .refine _ _ =>
      throw "datatype field declarations use unrefined types; refine program types instead"

private def validateMeasureBody (datatype : DataDecl) (ctor : CtorDecl)
    (body : MeasureBody) : Except String Unit := do
  match body with
  | .literal _ => pure ()
  | .field index =>
    let some field := ctor.fields[index]?
      | throw s!"measure reads nonexistent field {index} of '{ctor.name}'"
    if field.stripRefinements != .int then
      throw s!"measure field {index} of '{ctor.name}' must be Int"
  | .recur index =>
    let some field := ctor.fields[index]?
      | throw s!"measure recurses on nonexistent field {index} of '{ctor.name}'"
    match field.stripRefinements with
    | .data name _ =>
      if name != datatype.name then
        throw s!"measure recursion requires a direct '{datatype.name}' field"
    | _ => throw s!"measure recursion requires a direct '{datatype.name}' field"
  | .add left right =>
    validateMeasureBody datatype ctor left
    validateMeasureBody datatype ctor right

/-- Validate ordered positive datatype declarations, exhaustive structurally
recursive measures, and unique predicate signatures. Source-level type and
refinement checking additionally validates uses of these declarations. -/
private def validateCore (signature : Signature) (maxDepth : Nat := 256) : Except String Unit := do
  uniqueNames "datatype" (signature.datatypes.map (·.name))
  uniqueNames "constructor" (signature.datatypes.flatMap (fun d => d.ctors.map (·.name)))
  uniqueNames "measure" (signature.measures.map (·.name))
  uniqueNames "predicate" (signature.kvars.map (·.name))
  let mut earlier : List DataDecl := []
  for datatype in signature.datatypes do
    for ctor in datatype.ctors do
      for field in ctor.fields do
        validateField earlier datatype maxDepth 0 true field
    earlier := datatype :: earlier
  for measure in signature.measures do
    let some datatype := signature.findData measure.datatype
      | throw s!"measure '{measure.name}' refers to unknown datatype '{measure.datatype}'"
    uniqueNames s!"case in measure '{measure.name}'" (measure.cases.map (·.ctor))
    if measure.cases.length != datatype.ctors.length then
      throw s!"measure '{measure.name}' must cover every constructor exactly once"
    for branch in measure.cases do
      let some ctor := datatype.ctors.find? (·.name == branch.ctor)
        | throw s!"constructor '{branch.ctor}' does not belong to '{datatype.name}'"
      validateMeasureBody datatype ctor branch.body

/-- Detailed diagnostics followed by an explicit structural formation
certificate. The model construction consumes this certificate rather than
assuming facts about the diagnostic checker's loops or fuel. -/
def validate (signature : Signature) (maxDepth : Nat := 256) : Except String Unit :=
  match validateCore signature maxDepth with
  | .error message => .error message
  | .ok () => if signature.modelReady then .ok () else
      .error "datatype declarations failed the semantic formation check"

theorem validate_modelReady (signature : Signature) (maxDepth : Nat)
    (accepted : signature.validate maxDepth = .ok ()) : signature.modelReady = true := by
  unfold validate at accepted
  split at accepted
  · contradiction
  · split at accepted <;> simp_all

end Signature
end LambdaRK

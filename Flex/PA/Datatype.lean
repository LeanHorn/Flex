import Smt
import Flex.CHC.Export

/-!
# Algebraic datatypes and uninterpreted functions for PA SMT queries

The scalar PA oracle encodes Int, Bool and Prop values. This module extends a single batch
with:

* **Datatypes.** A closed, non-indexed, non-class inductive instance (a Flux record, an
  enum-like inductive, `List (Int × Int)`, ...) becomes an SMT-LIB datatype. Parametric
  types are monomorphized: every concrete instance gets its own sort `dt<i>`, with
  constructors `dt<i>_c<j>`, selectors `dt<i>_c<j>_<k>` and testers `is-dt<i>_c<j>`.
  Recursive and mutually/nested recursive types share one `declare-datatypes` block. A type
  is accepted only when every constructor field is Int, Bool, a Prop value or another
  accepted datatype, so the SMT datatype is exactly Lean's inductive type and `sat` stays
  conclusive. Function fields, proof fields, dependent fields, `Nat`, `String` and other
  builtins are rejected.
* **Uninterpreted functions.** An application of a constant that no other translator
  handles, whose value arguments and result have encodable sorts, becomes a `declare-fun`
  `uf<i>`. Closed non-value arguments (types, instances, closed lambdas) select the
  function; proofs are dropped. The function's meaning is lost, so `sat` answers of queries
  using one are inconclusive.

The registry is created per batch and reached from the translators through `registryExt`;
outside a PA batch the translators decline every term.
-/

namespace Flex.PA.Datatype

open Lean Meta Smt Translator Term

structure Constructor where
  name : Name
  smt : String
  /-- Selector symbols and their SMT sorts, in field order. -/
  fields : Array (String × String)
  deriving Inhabited

structure Datatype where
  smt : String
  /-- The closed, weak-head-normal Lean type `I params`. -/
  type : Expr
  ctors : Array Constructor := #[]
  deriving Inhabited

structure Function where
  smt : String
  arguments : Array String
  result : String
  deriving Inhabited

structure Registry where
  datatypes : Array Datatype := #[]
  byType : Std.HashMap Expr Nat := {}
  failed : Std.HashSet Expr := {}
  functions : Array Function := #[]
  byKey : Std.HashMap Expr Nat := {}
  /-- Counter for `let`-bound pattern variables. -/
  locals : Nat := 0
  deriving Inhabited

initialize registryExt : EnvExtension (Option (IO.Ref Registry)) ←
  registerEnvExtension (pure none) (asyncMode := .local)

def registry? : CoreM (Option (IO.Ref Registry)) :=
  return registryExt.getState (← getEnv)

/-- Types with dedicated SMT theories or literal representations; never generic datatypes. -/
private def builtin : Std.HashSet Name := .ofList [
  ``Nat, ``Int, ``Bool, ``String, ``Char, ``BitVec, ``Fin, ``UInt8, ``UInt16, ``UInt32,
  ``UInt64, ``USize, ``Float, ``Float32, ``Decidable, ``PUnit, ``PLift, ``ULift]

/-- Every datatype must have a finite inhabitant, otherwise z3 rejects the declaration. -/
private def allInhabited (registry : Registry) : Bool := Id.run do
  let mut inhabited : Std.HashSet String := .ofList ["Int", "Bool"]
  let mut changed := true
  while changed do
    changed := false
    for datatype in registry.datatypes do
      if inhabited.contains datatype.smt then continue
      if datatype.ctors.any (·.fields.all fun (_, sort) => inhabited.contains sort) then
        inhabited := inhabited.insert datatype.smt
        changed := true
  return registry.datatypes.all (inhabited.contains ·.smt)

private def reject (type : Expr) (why : String) : MetaM α :=
  throwError "PA SMT: unsupported datatype {type}: {why}"

mutual
/-- SMT sort of a constructor field or input; registers datatypes on the way. -/
private partial def sortCore (ref : IO.Ref Registry) (type : Expr) : MetaM String := do
  let type ← whnf type
  if type.isConstOf ``Int then return "Int"
  if type.isConstOf ``Bool || type.isProp then return "Bool"
  declare ref type

private partial def declare (ref : IO.Ref Registry) (type : Expr) : MetaM String := do
  let type ← instantiateMVars type
  let registry ← ref.get
  if let some i := registry.byType[type]? then return registry.datatypes[i]!.smt
  if registry.failed.contains type then reject type "previously rejected"
  if type.hasFVar || type.hasMVar || type.hasLooseBVars then reject type "open type"
  let .const name levels := type.getAppFn | reject type "not an inductive type"
  if builtin.contains name then reject type "builtin type"
  let env ← getEnv
  let some (.inductInfo info) := env.find? name | reject type "not an inductive type"
  if info.numIndices != 0 then reject type "indexed family"
  if info.isUnsafe || isClass env name then reject type "class or unsafe"
  if info.ctors.isEmpty then reject type "no constructors"
  if type.getAppNumArgs != info.numParams then reject type "partially applied"
  if ← isProp type then reject type "proposition"
  -- Instances that differ only up to definitional equality share one sort.
  for datatype in registry.datatypes do
    if datatype.type.getAppFn == type.getAppFn then
      if ← withNewMCtxDepth (isDefEq datatype.type type) then
        ref.modify fun r => { r with byType := r.byType.insert type (r.byType[datatype.type]!) }
        return datatype.smt
  let index := registry.datatypes.size
  let smt := s!"dt{index}"
  ref.modify fun r => { r with
    datatypes := r.datatypes.push { smt, type }
    byType := r.byType.insert type index }
  let mut ctors := #[]
  for ctorName in info.ctors, j in [:info.ctors.length] do
    let ctorType ← inferType (mkAppN (mkConst ctorName levels) type.getAppArgs)
    let sorts ← forallTelescopeReducing ctorType fun fields _ => do
      let mut sorts := #[]
      for field in fields do
        let fieldType ← inferType field
        if fieldType.hasAnyFVar (fun id => fields.contains (mkFVar id)) then reject type "dependent field"
        if ← isProp fieldType then reject type "proof field"
        sorts := sorts.push (← sortCore ref fieldType)
      return sorts
    let ctor := s!"{smt}_c{j}"
    ctors := ctors.push { name := ctorName, smt := ctor
                          fields := sorts.mapIdx fun k sort => (s!"{ctor}_{k}", sort) }
  ref.modify fun r => { r with datatypes := r.datatypes.set! index { smt, type, ctors } }
  return smt
end

/-- SMT sort of a value type: Int, Bool, Prop, or a registered datatype. Without a batch
registry only Int, Bool and Prop are accepted. A rejected type leaves the registry as it was. -/
def sortOf (type : Expr) : MetaM String := do
  let some ref ← registry? | return match ← CHC.Fragment.valueSort type with
    | .int => "Int" | .bool => "Bool"
  let saved ← ref.get
  try
    let sort ← sortCore ref type
    unless allInhabited (← ref.get) do throwError "PA SMT: datatype {type} has no finite value"
    return sort
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    let key ← instantiateMVars (← whnf type)
    ref.set { saved with failed := saved.failed.insert key }
    throw error

/-- The registered datatype of a value type, if it is encodable. -/
private def datatypeOf? (type : Expr) : TranslationM (Option Datatype) := do
  let some ref ← registry? | return none
  let sort ← try sortOf type catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none
  return (← ref.get).datatypes.find? (·.smt == sort)

private def isType (e : Expr) : MetaM Bool := do
  return (← whnf (← inferType e)).isSort

/-- Datatype sorts, plus type aliases of Int and Bool. -/
def translateType : Translator := fun e => do
  let some _ ← registry? | return none
  unless e.isApp || e.isConst do return none
  if e.isConstOf ``Int || e.isConstOf ``Bool then return none
  unless ← isType e do return none
  if ← isProp e then return none
  let some datatype ← datatypeOf? e | do
    let reduced ← whnf e
    if reduced.isConstOf ``Int then return some (symbolT "Int")
    if reduced.isConstOf ``Bool then return some (symbolT "Bool")
    return none
  return some (symbolT datatype.smt)

def translateConstructor : Translator := fun e => do
  let some _ ← registry? | return none
  let .const name _ := e.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  unless e.getAppNumArgs == info.numParams + info.numFields do return none
  if builtin.contains info.induct then return none
  let some datatype ← datatypeOf? (← inferType e) | return none
  let some ctor := datatype.ctors[info.cidx]? | return none
  unless ctor.name == name do return none
  let fields ← e.getAppArgs[info.numParams:].toArray.mapM applyTranslators!
  return some (fields.foldl appT (symbolT ctor.smt))

/-- Structure projections, as `Expr.proj` or as applied projection functions. -/
def translateProjection : Translator := fun e => do
  let some _ ← registry? | return none
  let some (index, value) ← match e with
      | .proj _ index value => pure (some (index, value))
      | _ => do
        let .const name _ := e.getAppFn | pure none
        let some info ← getProjectionFnInfo? name | pure none
        if info.fromClass || e.getAppNumArgs != info.numParams + 1 then pure none
        else pure (some (info.i, e.appArg!))
    | return none
  let some datatype ← datatypeOf? (← inferType value) | return none
  unless datatype.ctors.size == 1 do return none
  let some (selector, _) := datatype.ctors[0]!.fields[index]? | return none
  return some (appT (symbolT selector) (← applyTranslators! value))

/-- Bind a constructor's fields to `let`-bound selector applications, then translate. -/
private partial def branch (ref : IO.Ref Registry) (selectors : List String) (major : Smt.Term)
    (type minor : Expr) (extra : Array Expr) : TranslationM Smt.Term := do
  match selectors with
  | [] => applyTranslators! (mkAppN minor extra).headBeta
  | selector :: rest =>
    let .forallE _ domain codomain _ ← whnf type
      | throwError "PA SMT: malformed constructor type {type}"
    let n ← ref.modifyGet fun r => (r.locals, { r with locals := r.locals + 1 })
    let name := s!"pa_m{n}"
    Meta.withLocalDeclD (Name.mkSimple name) domain fun x => do
      modify fun s => { s with localFVars := s.localFVars.insert x.fvarId! }
      let body ← branch ref rest major (codomain.instantiate1 x) (minor.beta #[x]) extra
      modify fun s => { s with localFVars := s.localFVars.erase x.fvarId! }
      return letT name (appT (symbolT selector) major) body

/-- `casesOn` becomes `ite` over testers, with fields bound through selectors. -/
def translateCasesOn : Translator := fun e => do
  let some ref ← registry? | return none
  let .const name _ := e.getAppFn | return none
  let env ← getEnv
  unless isCasesOnRecursor env name do return none
  let some (.inductInfo info) := env.find? name.getPrefix | return none
  let args := e.getAppArgs
  let majorIndex := info.numParams + 1 + info.numIndices
  let arity := majorIndex + 1 + info.ctors.length
  if args.size < arity then return none
  let major := args[majorIndex]!
  let some datatype ← datatypeOf? (← inferType major) | return none
  let .const _ levels := datatype.type.getAppFn | return none
  let majorTerm ← applyTranslators! major
  let extra := args[arity:].toArray
  let mut branches := #[]
  for ctor in datatype.ctors, j in [:datatype.ctors.size] do
    let ctorType ← inferType (mkAppN (mkConst ctor.name levels) datatype.type.getAppArgs)
    branches := branches.push (← branch ref (ctor.fields.map (·.1)).toList majorTerm ctorType
      args[majorIndex + 1 + j]! extra)
  let mut result := branches.back!
  for j in (List.range (branches.size - 1)).reverse do
    result := mkApp3 (symbolT "ite") (appT (symbolT s!"is-{datatype.ctors[j]!.smt}") majorTerm)
      branches[j]! result
  return some result

/-- Pattern-matching auxiliaries unfold to `casesOn`. -/
def translateMatcher : Translator := fun e => do
  let some _ ← registry? | return none
  let .const name _ := e.getAppFn | return none
  let some info ← getMatcherInfo? name | return none
  if e.getAppNumArgs < info.arity then return none
  let some unfolded ← CHC.Prepare.unfoldMatcher? e | return none
  applyTranslators? unfolded

private def proofArgument : Expr := .const `_pa_proof []

/-- Last resort: an unknown constant applied to encodable values is an uninterpreted
function. Every other translator is tried first, whichever order lean-smt uses. -/
def translateUninterpreted : Translator := fun e => do
  let some ref ← registry? | return none
  let .const name _ := e.getAppFn | return none
  let env ← getEnv
  match env.find? name with
  | some (.defnInfo _) | some (.opaqueInfo _) | some (.axiomInfo _) | some (.thmInfo _) => pure ()
  | _ => return none
  if isCasesOnRecursor env name || (← getMatcherInfo? name).isSome then return none
  if let some info ← getProjectionFnInfo? name then
    unless info.fromClass do return none
  for (translator, translatorName) in ← getTranslators do
    if translatorName == `Flex.PA.Datatype.translateUninterpreted then continue
    try
      if let some term ← translator e then return some term
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
  if ← isType e then return none
  let result ← try sortOf (← inferType e) catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none
  let mut key := #[]
  let mut sorts := #[]
  let mut values := #[]
  for argument in e.getAppArgs do
    if ← isProof argument then
      key := key.push proofArgument
      continue
    let sort? ← if ← isType argument then pure none else
      try pure (some (← sortOf (← inferType argument))) catch error =>
        if error.isInterrupt || error.isRuntime then throw error
        pure none
    match sort? with
    | some sort =>
      key := key.push (.const (Name.mkSimple s!"_pa_arg{values.size}") [])
      sorts := sorts.push sort
      values := values.push argument
    | none =>
      if argument.hasFVar || argument.hasMVar || argument.hasLooseBVars then return none
      key := key.push argument
  let functionKey := mkAppN e.getAppFn key
  let terms ← values.mapM applyTranslators!
  let smt ← ref.modifyGet fun r => match r.byKey[functionKey]? with
    | some i => (r.functions[i]!.smt, r)
    | none =>
      let smt := s!"uf{r.functions.size}"
      (smt, { r with
        functions := r.functions.push { smt, arguments := sorts, result }
        byKey := r.byKey.insert functionKey r.functions.size })
  return some (terms.foldl appT (symbolT smt))

def translators : Array Name := #[``translateType, ``translateConstructor,
  ``translateProjection, ``translateCasesOn, ``translateMatcher, ``translateUninterpreted]

/-- Run `action` with a fresh registry and the datatype translators enabled. -/
def withRegistry (action : IO.Ref Registry → MetaM α) : MetaM α := do
  let ref ← IO.mkRef ({} : Registry)
  withoutModifyingEnv do
    modifyEnv fun env => registryExt.setState env (some ref)
    modifyEnv fun env => Smt.Attribute.smtExt.modifyState env fun state =>
      state.insert ``Smt.Translator (translators.foldl (·.insert ·) (state.getD ``Smt.Translator {}))
    action ref

/-- `declare-datatypes` for every registered datatype (one mutually recursive block), and
`declare-fun` for every uninterpreted function. -/
def Registry.datatypeCommands (registry : Registry) : String := Id.run do
  if registry.datatypes.isEmpty then return ""
  let sorts := registry.datatypes.map fun d => s!"({d.smt} 0)"
  let bodies := registry.datatypes.map fun d =>
    let ctors := d.ctors.map fun c =>
      if c.fields.isEmpty then s!"({c.smt})"
      else s!"({c.smt} {" ".intercalate (c.fields.map fun (s, sort) => s!"({s} {sort})").toList})"
    s!"({" ".intercalate ctors.toList})"
  return s!"(declare-datatypes ({" ".intercalate sorts.toList}) ({" ".intercalate bodies.toList}))\n"

def Registry.functionCommands (registry : Registry) : String :=
  "".intercalate (registry.functions.map fun f =>
    s!"(declare-fun {f.smt} ({" ".intercalate f.arguments.toList}) {f.result})\n").toList

/-- Symbols the registry adds, with their arities. -/
def Registry.symbols (registry : Registry) : Array (String × Nat) := Id.run do
  let mut symbols := #[]
  for datatype in registry.datatypes do
    for ctor in datatype.ctors do
      symbols := symbols.push (ctor.smt, ctor.fields.size) |>.push (s!"is-{ctor.smt}", 1)
      for (selector, _) in ctor.fields do symbols := symbols.push (selector, 1)
  for function in registry.functions do
    symbols := symbols.push (function.smt, function.arguments.size)
  return symbols

def Registry.sorts (registry : Registry) : Array String :=
  registry.datatypes.map (·.smt)

/-- Whether a term mentions an uninterpreted function, making `sat` inconclusive. -/
partial def usesFunctions : Smt.Term → Bool
  | .symbolT name => name.startsWith "uf"
  | .appT f x => usesFunctions f || usesFunctions x
  | .arrowT a b => usesFunctions a || usesFunctions b
  | .forallT _ _ body | .existsT _ _ body => usesFunctions body
  | .letT _ value body => usesFunctions value || usesFunctions body
  | .literalT _ => false

end Flex.PA.Datatype

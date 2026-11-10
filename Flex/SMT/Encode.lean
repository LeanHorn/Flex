import Lean

/-!
# Exact SMT-LIB encoding

Translate Lean propositions into SMT-LIB terms for z3, exactly whenever possible:

* `Int`, `Prop`/`Bool`, and `Nat` (as a nonnegative `Int`);
* non-dependent functions (`SmtMap`, `Arr`, function-valued variables) as `Array` sorts;
* non-indexed inductive types (records, `Option`, `List`, `Prod`, enumerations) as
  datatypes, monomorphized at each concrete instance;
* nonempty opaque types (stuck on an `opaque` constant or axiom) as uninterpreted sorts;
* definitions as `define-fun`, or as uninterpreted `declare-fun` symbols when they are
  recursive, when `flex.smt.uninterpretedDefs` is set, or when their body uses a construct
  that is not encoded.

Clauses have the form `∀ xs, premises → head`: `encodeClause` declares the prefix variables as
constants, asserts the premises and the negated head. Other quantifiers become SMT quantifiers.
Those the solver can skolemize are always encoded: existentials in asserted facts and premises,
and universals in the negated head. Any other quantifier, and any quantifier under a non-logical
operator or in a definition body (where its polarity is mixed or unknown), needs
`flex.smt.encodeQuantifiers`.

Encoding never silently changes meaning. Constructs that cannot be encoded raise an error.
Abstractions (uninterpreted symbols, `Nat` values inside containers) are recorded, so callers
can treat a satisfiable result as inconclusive.
-/

register_option flex.smt.uninterpretedDefs : Bool := {
  defValue := false
  descr := "Encode every non-reducible definition as an uninterpreted SMT function."
}

register_option flex.smt.encodeNonlinear : Bool := {
  defValue := false
  descr := "Encode non-linear arithmetic (products of non-literals, division or modulo by \
    a non-literal). When off, queries using it are not sent to the solver and definitions \
    using it become uninterpreted."
}

register_option flex.smt.encodeQuantifiers : Bool := {
  defValue := false
  descr := "Encode quantifiers and lambdas left after flattening clauses. When off, queries using \
    them are not sent to the solver and definitions using them become uninterpreted."
}

namespace Flex.SMT

open Lean Meta

structure Config where
  uninterpretedDefs : Bool := false
  encodeNonlinear : Bool := false
  encodeQuantifiers : Bool := false
  /-- Emit Horn clauses (`encodeHornClause`): every variable is a clause binder, and nothing
  may be uninterpreted, since CHC solvers read uninterpreted symbols as predicates or reject them. -/
  horn : Bool := false
  deriving Inhabited, Repr

def Config.ofOptions (options : Options) : Config where
  uninterpretedDefs := flex.smt.uninterpretedDefs.get options
  encodeNonlinear := flex.smt.encodeNonlinear.get options
  encodeQuantifiers := flex.smt.encodeQuantifiers.get options

/-- A monomorphized datatype instance. -/
structure Datatype where
  symbol : String
  /-- Constructor name, SMT constructor symbol and SMT selector symbols. -/
  constructors : Array (Name × String × Array String)
  deriving Inhabited

/-- An encoded definition instance. -/
structure Definition where
  symbol : String
  /-- Whether using it abstracts: it is uninterpreted, or its body uses an abstraction. -/
  abstracted : Bool
  /-- Nullary definitions whose body is a numeral are inlined. -/
  literal? : Option String := none
  deriving Inhabited

structure State where
  /-- Global declarations, in dependency order. -/
  declarations : Array String := #[]
  /-- Global assertions about declared symbols, such as `Nat` nonnegativity. -/
  axioms : Array String := #[]
  sorts : Std.HashMap Expr String := {}
  /-- Sorts whose SMT values include values that do not exist in Lean. -/
  lossySorts : Std.HashSet String := {}
  datatypes : Std.HashMap Expr Datatype := {}
  /-- Datatypes whose declaration is being built, innermost last. -/
  pendingDatatypes : Array Expr := #[]
  definitions : Std.HashMap Expr Definition := {}
  pendingDefinitions : Std.HashSet Expr := {}
  names : Std.HashMap FVarId String := {}
  lossyNames : Std.HashSet String := {}
  counter : Nat := 0
  /-- Whether the current encoding uses an abstraction. -/
  abstracted : Bool := false
  /-- Horn relation symbols applied so far. -/
  usedRelations : Std.HashSet String := {}
  deriving Inhabited

/-- Where a formula ends up in the solver's input: asserted (`pos`), under a negation (`neg`),
or both or unknown (`both`). -/
inductive Polarity where
  | pos | neg | both
  deriving BEq, Inhabited

def Polarity.flip : Polarity → Polarity
  | .pos => .neg
  | .neg => .pos
  | .both => .both

structure Context where
  config : Config
  polarity : Polarity := .both
  /-- Local predicate symbols encoded as Horn relation applications. -/
  relations : Std.HashMap FVarId String := {}

abbrev EncodeM := ReaderT Context (StateRefT State MetaM)

private def markAbstracted : EncodeM Unit :=
  modify fun s => { s with abstracted := true }

private def sanitize (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.toNat > 32 && c.toNat < 127 && c != '|' && c != '\\' then acc.push c
    else acc ++ s!"_u{c.toNat}"

/-- A fresh quoted SMT symbol. Counters keep symbols unique even when names collide. -/
def fresh (base : String) : EncodeM String := do
  let n := (← get).counter
  modify fun s => { s with counter := n + 1 }
  return s!"|{sanitize base}!{n}|"

private def declare (command : String) : EncodeM Unit :=
  modify fun s => { s with declarations := s.declarations.push command }

/-- Integer numerals, as printed by this encoder. -/
def isNumeral (s : String) : Bool :=
  let cs := s.toList
  let digits (t : List Char) := !t.isEmpty && t.all Char.isDigit
  digits cs || (cs.take 3 == ['(', '-', ' '] && cs.getLast? == some ')' && digits ((cs.drop 3).dropLast))

private def unsupported (what : MessageData) : EncodeM α :=
  throwError m!"SMT encoding: unsupported {what}"

private def isNatType (type : Expr) : MetaM Bool := do
  return (← whnf type).isConstOf ``Nat

/-! ## Sorts -/

/-- Whether `type` is stuck on an opaque constant or axiom (possibly through projections), so that
Lean exposes nothing about it but equality, e.g. `opaque C : (α : Type) × Inhabited α`, `C.1`. -/
partial def isOpaqueType (type : Expr) : MetaM Bool := do
  match type.getAppFn.consumeMData with
  | .proj _ _ struct => isOpaqueType struct
  | .const name _ =>
    match (← getEnv).find? name with
    | some (.opaqueInfo _) | some (.axiomInfo _) => return true
    | _ => return false
  | _ => return false

/-- Normalize a closed type so that definitionally equal sorts share one SMT declaration:
reduce the head and, recursively, every type argument and function domain/codomain
(e.g. `Option (ASeq Int Int)` and `Option (List (Int × Int))`). -/
partial def canonicalType (type : Expr) : MetaM Expr := do
  let type ← whnf (← instantiateMVars type).consumeMData
  match type with
  | .forallE n d b bi =>
    if b.hasLooseBVars then return type
    return .forallE n (← canonicalType d) (← canonicalType b) bi
  | _ =>
    let fn := type.getAppFn
    unless fn.isConst do return type
    let args ← type.getAppArgs.mapM fun a => do
      if (← inferType a).isSort then canonicalType a else pure a
    return mkAppN fn args

mutual

/-- Encode a closed Lean type as an SMT sort. -/
partial def encodeSort (type : Expr) : EncodeM String := do
  let type ← instantiateMVars type
  let type := type.consumeMData
  if type.hasLooseBVars || type.hasFVar || type.hasMVar then
    unsupported m!"open sort {type}"
  let reduced ← canonicalType type
  let pending := (← get).pendingDatatypes
  if pending.contains reduced then
    -- Only a direct self-reference of the datatype being declared is well-formed.
    if pending.back? == some reduced then return (← get).sorts[reduced]!
    unsupported m!"nested inductive occurrence of {type}"
  if let some sort := (← get).sorts[type]? <|> (← get).sorts[reduced]? then
    if (← get).lossySorts.contains sort then markAbstracted
    return sort
  let (sort, lossy) ← match reduced with
    | .sort .zero => pure ("Bool", false)
    | .const ``Int _ => pure ("Int", false)
    | .const ``Nat _ => pure ("Int", false)
    | .const ``Bool _ => pure ("Bool", false)
    | .forallE _ domain body _ =>
      if body.hasLooseBVars then unsupported m!"dependent function sort {type}"
      let index ← encodeSort domain
      let element ← encodeSort body
      let lossy := (← isNatType domain) || (← isNatType body) ||
        (← get).lossySorts.contains index || (← get).lossySorts.contains element
      pure (s!"(Array {index} {element})", lossy)
    | _ =>
      -- An opaque type is exactly an uninterpreted sort, provided it is nonempty, as every
      -- SMT sort is: a possibly empty type could make a universal premise vacuous.
      if ← isOpaqueType reduced then
        if (← read).config.horn then unsupported m!"opaque sort {type} in a Horn clause"
        -- Instances are usually declared for the type as written, not its reduced form.
        let nonempty ← [type, reduced].anyM fun t => do
          try pure (← synthInstance? (← mkAppM ``Nonempty #[t])).isSome catch _ => pure false
        unless nonempty do unsupported m!"opaque sort {type} without a Nonempty instance"
        let symbol ← fresh s!"{← ppExpr type}"
        declare s!"(declare-sort {symbol} 0)"
        pure (symbol, false)
      else
      let datatype ← encodeDatatype reduced
      pure (datatype.symbol, (← get).lossySorts.contains datatype.symbol)
  modify fun s => { s with
    sorts := (s.sorts.insert type sort).insert reduced sort
    lossySorts := if lossy then s.lossySorts.insert sort else s.lossySorts }
  if lossy then markAbstracted
  return sort

/-- Declare a monomorphized instance of a non-indexed inductive type. -/
partial def encodeDatatype (type : Expr) : EncodeM Datatype := do
  -- Constructor and projection terms reach this with unnormalized type arguments.
  let type ← canonicalType type
  if let some datatype := (← get).datatypes[type]? then return datatype
  let .const name levels := type.getAppFn | unsupported m!"sort {type}"
  let some (.inductInfo info) := (← getEnv).find? name | unsupported m!"sort {type}"
  if (← inferType type) == mkSort .zero then unsupported m!"propositional type {type}"
  if info.numIndices != 0 then unsupported m!"indexed inductive {name}"
  if info.all.length > 1 then unsupported m!"mutual inductive {name}"
  if info.ctors.isEmpty then unsupported m!"empty inductive {name}"
  let params := type.getAppArgs
  unless params.size == info.numParams do unsupported m!"partially applied sort {type}"
  if (← get).pendingDatatypes.contains type then
    unsupported m!"nested inductive occurrence of {type}"
  let suffix ← params.filterMapM fun p => do
    if (← inferType p).isSort then return some (toString (← ppExpr p)) else return none
  let base := if suffix.isEmpty then name.toString else s!"{name}<{", ".intercalate suffix.toList}>"
  let symbol ← fresh base
  -- Register the symbol first, so direct self-references in fields resolve to it.
  modify fun s => { s with
    sorts := s.sorts.insert type symbol
    pendingDatatypes := s.pendingDatatypes.push type }
  try
    let mut constructors := #[]
    let mut declarations := #[]
    let mut lossy := false
    for ctorName in info.ctors do
      let ctor ← getConstInfoCtor ctorName
      let ctorType ← instantiateForall (← instantiateTypeLevelParams ctor.toConstantVal levels) params
      let ctorSymbol ← fresh s!"{base}.{ctorName.getString!}"
      let mut fields := ctorType
      let mut selectors := #[]
      let mut fieldDeclarations := #[]
      for i in [:ctor.numFields] do
        let .forallE fieldName domain body _ := fields
          | unsupported m!"constructor {ctorName}"
        if domain.hasLooseBVars || body.hasLooseBVar 0 then
          unsupported m!"dependent field of {ctorName}"
        if ← isProp domain then unsupported m!"proof field of {ctorName}"
        let sort ← encodeSort domain
        if (← isNatType domain) || (← get).lossySorts.contains sort then lossy := true
        let fieldBase := if fieldName.isAnonymous then s!"field{i}" else fieldName.toString
        let selector ← fresh s!"{base}.{ctorName.getString!}.{fieldBase}"
        selectors := selectors.push selector
        fieldDeclarations := fieldDeclarations.push s!"({selector} {sort})"
        fields := body.lowerLooseBVars 1 1
      constructors := constructors.push (ctorName, ctorSymbol, selectors)
      declarations := declarations.push
        (if selectors.isEmpty then s!"({ctorSymbol})"
         else s!"({ctorSymbol} {" ".intercalate fieldDeclarations.toList})")
    declare s!"(declare-datatypes (({symbol} 0)) (({" ".intercalate declarations.toList})))"
    let datatype := { symbol, constructors }
    modify fun s => { s with
      datatypes := s.datatypes.insert type datatype
      pendingDatatypes := s.pendingDatatypes.pop
      lossySorts := if lossy then s.lossySorts.insert symbol else s.lossySorts }
    return datatype
  catch error =>
    modify fun s => { s with
      sorts := s.sorts.erase type
      pendingDatatypes := s.pendingDatatypes.erase type }
    throw error

end

/-! ## Terms -/

/-- Unfold a class operation through its instance, e.g. `a + b` on `Int` to `Int.add a b`. Unlike
`unfoldProjInst?`, instances built by plain definitions (such as `minOfLe`) also unfold. -/
private def unfoldClassOperation? (e : Expr) : MetaM (Option Expr) := do
  let some e ← withDefault <| unfoldDefinition? e | return none
  let some field ← withDefault <| reduceProj? e.getAppFn | return none
  return some (mkAppN field e.getAppArgs).headBeta

/-- Open a definition's value parameters as local variables, instantiating static ones. -/
private partial def openParams (name : Name) (static : Array (Option Expr)) (type : Expr) (i : Nat)
    (xs fixed : Array Expr) (k : Array Expr → Array Expr → Expr → EncodeM α) : EncodeM α := do
  if h : i < static.size then
    let type ← whnf type
    let .forallE binder domain body bi := type | unsupported m!"definition type {name}"
    match static[i] with
    | some argument => openParams name static (body.instantiate1 argument) (i + 1) xs (fixed.push argument) k
    | none =>
      withLocalDecl binder bi domain fun x =>
        openParams name static (body.instantiate1 x) (i + 1) (xs.push x) (fixed.push x) k
  else k xs fixed type

/-- Primitive `Int`/`Nat` arithmetic: the operation and whether it is on `Int`. -/
private def arithmeticOperation? : Name → Option (Name × Bool)
  | ``Int.add => some (``HAdd.hAdd, true) | ``Nat.add => some (``HAdd.hAdd, false)
  | ``Int.sub => some (``HSub.hSub, true) | ``Nat.sub => some (``HSub.hSub, false)
  | ``Int.mul => some (``HMul.hMul, true) | ``Nat.mul => some (``HMul.hMul, false)
  | ``Int.ediv => some (``HDiv.hDiv, true) | ``Nat.div => some (``HDiv.hDiv, false)
  | ``Int.emod => some (``HMod.hMod, true) | ``Nat.mod => some (``HMod.hMod, false)
  | _ => none

private def requireQuantifiers (what : String) : EncodeM Unit := do
  unless (← read).config.encodeQuantifiers do
    throwError "SMT encoding: {what} (flex.smt.encodeQuantifiers is off)"

def withPolarity (polarity : Polarity) (k : EncodeM α) : EncodeM α :=
  withReader (fun ctx => { ctx with polarity }) k

private def flipped (k : EncodeM α) : EncodeM α :=
  withReader (fun ctx => { ctx with polarity := ctx.polarity.flip }) k

/-- Logical connectives pass polarity to their arguments; any other operator mixes it. -/
private def isConnective (name : Name) : Bool :=
  [``True, ``False, ``Not, ``And, ``Or, ``Exists, ``ite, ``dite].contains name

mutual

/-- Encode `e` as an SMT term. Every quantifier and non-array lambda in `e` is encoded as an
SMT binder; clause prefixes are opened by `encodeClause` instead. -/
partial def encode (e : Expr) : EncodeM String := do
  let e := e.consumeMData
  match e with
  | .fvar id => encodeFVar id
  | .lit (.natVal n) => return toString n
  | .lit (.strVal _) => unsupported m!"string literal"
  | .letE _ _ value body _ => encode (body.instantiate1 value)
  | .forallE name domain body bi => encodeForall name domain body bi
  | .lam .. => encodeLambda e
  | .proj structName index value => do
    let datatype ← encodeDatatype (← whnf (← inferType value))
    let some (_, _, selectors) := datatype.constructors[0]? | unsupported m!"projection of {structName}"
    let some selector := selectors[index]? | unsupported m!"projection of {structName}"
    return s!"({selector} {← encode value})"
  | .const name levels => encodeApp e (.const name levels) #[]
  | .app .. =>
    let fn := e.getAppFn.consumeMData
    if fn.isLambda then return ← encode e.headBeta
    encodeApp e fn e.getAppArgs
  | _ => unsupported m!"term {e}"

partial def encodeFVar (id : FVarId) : EncodeM String := do
  if let some name := (← get).names[id]? then
    if (← get).lossyNames.contains name then markAbstracted
    return name
  if let some symbol := (← read).relations[id]? then
    modify fun s => { s with usedRelations := s.usedRelations.insert symbol }
    return symbol
  let decl ← id.getDecl
  if let some value := decl.value? then return ← encode value
  if ← isProof (mkFVar id) then unsupported m!"proof term {decl.userName}"
  if (← read).config.horn then unsupported m!"free variable {decl.userName} in a Horn clause"
  let sort ← encodeSort decl.type
  let lossy := (← get).lossySorts.contains sort
  let name ← fresh decl.userName.toString
  declare s!"(declare-const {name} {sort})"
  if ← isNatType decl.type then
    modify fun s => { s with axioms := s.axioms.push s!"(assert (>= {name} 0))" }
  modify fun s => { s with
    names := s.names.insert id name
    lossyNames := if lossy then s.lossyNames.insert name else s.lossyNames }
  return name

/-- Bind `x` to the SMT symbol `name`. -/
partial def withBinder (x : Expr) (name : String) (k : EncodeM α) : EncodeM α := do
  modify fun s => { s with names := s.names.insert x.fvarId! name }
  k

partial def encodeForall (name : Name) (domain body : Expr) (bi : BinderInfo)
    : EncodeM String := do
  if ← isProp domain then
    if body.hasLooseBVar 0 then unsupported m!"proof-dependent implication"
    return s!"(=> {← flipped (encode domain)} {← encode (body.lowerLooseBVars 1 1)})"
  encodeQuantifier true name domain bi fun x => encode (body.instantiate1 x)

/-- Encode `∀`/`∃` over data as an SMT quantifier. The solver skolemizes asserted existentials
and negated universals, so those are always encoded; others need `encodeQuantifiers`. -/
partial def encodeQuantifier (universal : Bool) (name : Name) (domain : Expr) (bi : BinderInfo)
    (body : Expr → EncodeM String) : EncodeM String := do
  let skolemized := (← read).polarity == if universal then .neg else .pos
  unless skolemized do
    requireQuantifiers (if universal then "universal quantifier" else "existential quantifier")
  let sort ← encodeSort domain
  let nat ← isNatType domain
  withLocalDecl name bi domain fun x => do
    let symbol ← fresh name.toString
    let encoded ← withBinder x symbol (body x)
    let quantifier := if universal then "forall" else "exists"
    let encoded := if !nat then encoded
      else if universal then s!"(=> (>= {symbol} 0) {encoded})"
      else s!"(and (>= {symbol} 0) {encoded})"
    return s!"({quantifier} (({symbol} {sort})) {encoded})"

/-- Functions as arrays: constant arrays, `store` updates, otherwise z3 lambdas. -/
partial def encodeLambda (e : Expr) : EncodeM String := withPolarity .both do
  let .lam name domain body bi := e | unsupported m!"term {e}"
  let sort ← encodeSort (← inferType e)
  withLocalDecl name bi domain fun x => do
    let body := (body.instantiate1 x).consumeMData
    let mentions (t : Expr) := t.containsFVar x.fvarId!
    if !mentions body then
      return s!"((as const {sort}) {← encode body})"
    if let some (key, value, map) ← storeUpdate? x body then
      unless mentions key || mentions value || mentions map do
        return s!"(store {← encode map} {← encode key} {← encode value})"
    requireQuantifiers "lambda"
    let symbol ← fresh name.toString
    let encoded ← withBinder x symbol (encode body)
    return s!"(lambda (({symbol} {← encodeSort domain})) {encoded})"

/-- Recognize `fun x => if x = k then v else m x`, including `==` with a lawful instance. -/
partial def storeUpdate? (x body : Expr) : EncodeM (Option (Expr × Expr × Expr)) := do
  unless body.isAppOfArity ``ite 5 do return none
  let condition := (body.getArg! 1).consumeMData
  let value := body.getArg! 3
  let rest := (body.getArg! 4).consumeMData
  unless rest.isApp && rest.appArg!.consumeMData == x do return none
  let map := rest.appFn!
  let key? ← do
    let condition := if let some (_, b, t) := condition.eq? then
        if t.isConstOf ``Bool.true then b.consumeMData else condition else condition
    if let some (_, a, b) := condition.eq? then
      if a.consumeMData == x then pure (some b) else if b.consumeMData == x then pure (some a) else pure none
    else if condition.isAppOfArity ``BEq.beq 4 && (condition.getArg! 2).consumeMData == x then
      let key := condition.getArg! 3
      let lawful ← try isDefEq condition (← mkDecide (← mkEq x key)) catch _ => pure false
      pure (if lawful then some key else none)
    else pure none
  return key?.map (·, value, map)

/-- Applications: logic, arithmetic, datatypes, definitions, and array reads. -/
partial def encodeApp (e fn : Expr) (args : Array Expr) : EncodeM String := do
  match fn with
  | .const name _ =>
    if isConnective name then encodeAppAt e fn args
    else withPolarity .both (encodeAppAt e fn args)
  | _ => withPolarity .both (encodeAppAt e fn args)

partial def encodeAppAt (e fn : Expr) (args : Array Expr) : EncodeM String := do
  match fn with
  | .const name levels =>
    let arg (i : Nat) := args[i]!
    let n := args.size
    match name, n with
    | ``True, 0 => return "true"
    | ``False, 0 => return "false"
    | ``Bool.true, 0 => return "true"
    | ``Bool.false, 0 => return "false"
    | ``Nat.zero, 0 => return "0"
    | ``Not, 1 => return s!"(not {← flipped (encode (arg 0))})"
    | ``And, 2 => return s!"(and {← encode (arg 0)} {← encode (arg 1)})"
    | ``Or, 2 => return s!"(or {← encode (arg 0)} {← encode (arg 1)})"
    | ``Iff, 2 => return s!"(= {← encode (arg 0)} {← encode (arg 1)})"
    | ``Eq, 3 =>
      discard <| encodeSort (arg 0)
      return s!"(= {← encode (arg 1)} {← encode (arg 2)})"
    | ``Ne, 3 =>
      discard <| encodeSort (arg 0)
      return s!"(not (= {← encode (arg 1)} {← encode (arg 2)}))"
    | ``ite, 5 =>
      return s!"(ite {← withPolarity .both (encode (arg 1))} {← encode (arg 3)} {← encode (arg 4)})"
    | ``dite, 5 =>
      let branch (b : Expr) : EncodeM String := do
        let .lam _ _ body _ := b.consumeMData | unsupported m!"dependent if-then-else"
        if body.hasLooseBVar 0 then unsupported m!"dependent if-then-else"
        encode (body.lowerLooseBVars 1 1)
      return s!"(ite {← withPolarity .both (encode (arg 1))} {← branch (arg 3)} {← branch (arg 4)})"
    | ``Exists, 2 =>
      let .lam binder domain body bi := (arg 1).consumeMData
        | unsupported m!"existential without a binder"
      if ← isProp domain then
        if body.hasLooseBVar 0 then unsupported m!"proof-dependent existential"
        return s!"(and {← encode domain} {← encode (body.lowerLooseBVars 1 1)})"
      encodeQuantifier false binder domain bi fun x => encode (body.instantiate1 x)
    | ``Decidable.decide, 2 => encode (arg 0)
    | ``and, 2 => return s!"(and {← encode (arg 0)} {← encode (arg 1)})"
    | ``or, 2 => return s!"(or {← encode (arg 0)} {← encode (arg 1)})"
    | ``not, 1 => return s!"(not {← encode (arg 0)})"
    | `Bool.xor, 2 | `xor, 2 => return s!"(xor {← encode (arg 0)} {← encode (arg 1)})"
    | ``bne, 4 => return s!"(not {← encode (mkApp4 (.const ``BEq.beq levels) (arg 0) (arg 1) (arg 2) (arg 3))})"
    -- Theory operations. Operator notation (`+`, `≤`, `min`, numerals, casts, …) reaches these
    -- by unfolding class instances in `encodeConstApp`; other instances follow the usual
    -- policy for definitions.
    | ``Int.neg, 1 => return s!"(- {← encode (arg 0)})"
    -- Direct calls (e.g. `i.le n`) would otherwise unfold to the opaque `Int.NonNeg`.
    | ``Int.le, 2 | ``Nat.le, 2 => return s!"(<= {← encode (arg 0)} {← encode (arg 1)})"
    | ``Int.lt, 2 | ``Nat.lt, 2 => return s!"(< {← encode (arg 0)} {← encode (arg 1)})"
    | ``Int.ofNat, 1 => encode (arg 0)
    | ``Int.negSucc, 1 => return s!"(- (- {← encode (arg 0)}) 1)"
    | ``Nat.succ, 1 => return s!"(+ {← encode (arg 0)} 1)"
    | ``Int.toNat, 1 => let a ← encode (arg 0); return s!"(ite (>= {a} 0) {a} 0)"
    | ``Int.natAbs, 1 => let a ← encode (arg 0); return s!"(ite (>= {a} 0) {a} (- {a}))"
    | _, 2 =>
      if let some (op, int) := arithmeticOperation? name then
        arithmetic op int (← encode (arg 0)) (← encode (arg 1))
      else encodeConstApp e name levels args
    | _, _ => encodeConstApp e name levels args
  | .fvar id =>
    if let some symbol := (← read).relations[id]? then
      modify fun s => { s with usedRelations := s.usedRelations.insert symbol }
      let encoded ← args.mapM fun a => encode a
      return if encoded.isEmpty then symbol else s!"({symbol} {" ".intercalate encoded.toList})"
    encodeReads e fn args
  | .proj .. | .app .. | .mdata .. => encodeReads e fn args
  | .mvar _ => unsupported m!"metavariable in {e}"
  | _ => unsupported m!"application {e}"

/-- Function-valued terms are arrays; each argument is one read. -/
partial def encodeReads (e fn : Expr) (args : Array Expr) : EncodeM String := do
  let mut result ← encode fn
  let mut type ← inferType fn
  for argument in args do
    let .forallE _ _ body _ ← whnf type | unsupported m!"application {e}"
    if body.hasLooseBVars then unsupported m!"dependent application {e}"
    if (← isProof argument) || (← isType argument) then unsupported m!"application {e}"
    result := s!"(select {result} {← encode argument})"
    type := body
  if (← isNatType (← inferType e)) then markAbstracted
  return result

/-- Linear arithmetic directly; non-linear operations only when enabled. Lean's `x / 0 = 0` and
`x % 0 = x` are kept exactly; SMT-LIB leaves division by zero unspecified. -/
partial def arithmetic (op : Name) (int : Bool) (a b : String) : EncodeM String := do
  let nonlinear (what : String) : EncodeM Unit := do
    unless (← read).config.encodeNonlinear do
      throwError "SMT encoding: non-linear {what} (flex.smt.encodeNonlinear is off)"
  match op with
  | ``HAdd.hAdd => return s!"(+ {a} {b})"
  | ``HSub.hSub => return if int then s!"(- {a} {b})" else s!"(ite (>= {a} {b}) (- {a} {b}) 0)"
  | ``HMul.hMul =>
    unless isNumeral a || isNumeral b do nonlinear "multiplication"
    return s!"(* {a} {b})"
  | ``HDiv.hDiv | ``HMod.hMod =>
    let div := op == ``HDiv.hDiv
    if isNumeral b then
      if b == "0" then return if div then "0" else a
      return if div then s!"(div {a} {b})" else s!"(mod {a} {b})"
    nonlinear (if div then "division" else "modulo")
    return if div then s!"(ite (= {b} 0) 0 (div {a} {b}))" else s!"(ite (= {b} 0) {a} (mod {a} {b}))"
  | _ => unsupported m!"arithmetic operator {op}"

/-- Constructors, projections, reducible abbreviations, and definitions. -/
partial def encodeConstApp (e : Expr) (name : Name) (levels : List Level) (args : Array Expr)
    : EncodeM String := do
  let env ← getEnv
  let some info := env.find? name | unsupported m!"unknown constant {name}"
  -- Constructors of encoded datatypes.
  if let .ctorInfo ctor := info then
    if args.size != ctor.numParams + ctor.numFields then unsupported m!"partial constructor {e}"
    let datatype ← encodeDatatype (← whnf (← inferType e))
    let some (_, symbol, _) := datatype.constructors.find? (·.1 == name)
      | unsupported m!"constructor {name}"
    let fields ← args[ctor.numParams:].toArray.mapM fun a => encode a
    return if fields.isEmpty then symbol else s!"({symbol} {" ".intercalate fields.toList})"
  -- Structure projections become selectors; class projections unfold their instance.
  if let some projection ← getProjectionFnInfo? name then
    if projection.fromClass then
      if let some unfolded ← unfoldClassOperation? e then return ← encode unfolded
      unsupported m!"class operation {name}"
    if args.size <= projection.numParams then unsupported m!"partial projection {e}"
    let value := args[projection.numParams]!
    let datatype ← encodeDatatype (← whnf (← inferType value))
    let some (_, _, selectors) := datatype.constructors[0]? | unsupported m!"projection {name}"
    let some selector := selectors[projection.i]? | unsupported m!"projection {name}"
    let read := s!"({selector} {← encode value})"
    return ← selects e read args[projection.numParams + 1:].toArray
  -- Reducible abbreviations are notation: always unfold them.
  if (← getReducibilityStatus name) == .reducible then
    if let some unfolded ← unfoldDefinition? e then return ← encode unfolded
  match info with
  | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
    if ← isProp info.type then unsupported m!"proof constant {name}"
    encodeDefinitionApp e name levels info args
  | _ => unsupported m!"constant {name}"

/-- Further reads from a function-valued result. -/
partial def selects (e : Expr) (head : String) (extra : Array Expr) : EncodeM String := do
  let mut result := head
  for argument in extra do
    if (← isProof argument) || (← isType argument) then unsupported m!"application {e}"
    result := s!"(select {result} {← encode argument})"
  if !extra.isEmpty && (← isNatType (← inferType e)) then markAbstracted
  return result

/-- Apply a definition, monomorphized on its type, instance and proof arguments. -/
partial def encodeDefinitionApp (e : Expr) (name : Name) (levels : List Level)
    (info : ConstantInfo) (args : Array Expr) : EncodeM String := do
  -- Classify binders: static (types, instances, proofs) or value parameters.
  let mut type ← instantiateTypeLevelParams info.toConstantVal levels
  let mut static : Array (Option Expr) := #[]
  let mut values : Array Expr := #[]
  let mut consumed := 0
  for argument in args do
    let type' ← whnf type
    let .forallE _ domain body _ := type' | break
    let isStatic := domain.isSort || (← isClass? domain).isSome || (← isProp domain)
    if isStatic then
      if argument.hasFVar || argument.hasMVar then unsupported m!"open type or instance argument in {e}"
      static := static.push (some argument)
    else
      static := static.push none
      values := values.push argument
    type := body.instantiate1 argument
    consumed := consumed + 1
  -- With fewer arguments than parameters, the instance returns an array.
  let key := mkAppN (.const name levels) (static.map (·.getD (mkSort .zero)))
  let definition ← try encodeDefinition key name levels info static
    catch error =>
      -- Horn clauses admit no uninterpreted symbols. A non-recursive definition whose body
      -- does not encode in general may still encode at this call, e.g. `a % b` at `b := 4`.
      if error.isInterrupt || error.isRuntime || !(← read).config.horn then throw error
      unless info matches .defnInfo _ do throw error
      if info.all.length > 1 || (← isRecursiveDefinition name) then throw error
      let some unfolded ← unfoldDefinition? e | throw error
      return ← encode unfolded
  if definition.abstracted then markAbstracted
  if let some literal := definition.literal? then return literal
  let encodedValues ← values.mapM fun a => encode a
  let head := if encodedValues.isEmpty then definition.symbol
    else s!"({definition.symbol} {" ".intercalate encodedValues.toList})"
  selects e head args[consumed:].toArray

/-- Declare one definition instance: `define-fun` when its body encodes, else `declare-fun`. -/
partial def encodeDefinition (key : Expr) (name : Name) (levels : List Level) (info : ConstantInfo)
    (static : Array (Option Expr)) : EncodeM Definition := do
  if let some definition := (← get).definitions[key]? then return definition
  if (← get).pendingDefinitions.contains key then unsupported m!"cyclic definition {name}"
  let type ← instantiateTypeLevelParams info.toConstantVal levels
  openParams name static type 0 #[] #[] fun params arguments result => do
    let paramSorts ← params.mapM fun x => do encodeSort (← inferType x)
    let resultSort ← encodeSort result
    let symbol ← fresh name.toString
    let lossy := (← paramSorts.anyM fun s => do return (← get).lossySorts.contains s) ||
      (← get).lossySorts.contains resultSort
    let recursive := info.all.length > 1 || (← isRecursiveDefinition name)
    let interpreted? ← do
      if (← read).config.uninterpretedDefs || recursive then pure none else
      match info with
      | .defnInfo _ =>
        let saved := (← get).abstracted
        modify fun s => { s with
          abstracted := false, pendingDefinitions := s.pendingDefinitions.insert key }
        let attempt ← try
            let value ← instantiateValueLevelParams info levels
            let body := (value.beta arguments).headBeta
            let names ← params.mapM fun x => do
              let n ← fresh (← x.fvarId!.getUserName).toString
              modify fun s => { s with names := s.names.insert x.fvarId! n }
              return n
            -- A definition may be used at either polarity.
            let encoded ← withPolarity .both (encode body)
            pure (some (names, encoded, (← get).abstracted))
          catch error =>
            if error.isInterrupt then throw error
            trace[flex.smt] "{name} is uninterpreted: {error.toMessageData}"
            pure none
        modify fun s => { s with
          abstracted := saved, pendingDefinitions := s.pendingDefinitions.erase key }
        pure attempt
      | _ => pure none
    let definition ← match interpreted? with
      | some (names, body, abstracted) =>
        if params.isEmpty && isNumeral body then
          pure { symbol, abstracted, literal? := some body }
        else
          let formals := (names.zip paramSorts).map fun (n, s) => s!"({n} {s})"
          declare s!"(define-fun {symbol} ({" ".intercalate formals.toList}) {resultSort} {body})"
          pure { symbol, abstracted := abstracted || lossy }
      | none =>
        if (← read).config.horn then
          unsupported m!"uninterpreted definition {name} in a Horn clause"
        declare s!"(declare-fun {symbol} ({" ".intercalate paramSorts.toList}) {resultSort})"
        pure { symbol, abstracted := true }
    modify fun s => { s with definitions := s.definitions.insert key definition }
    return definition

end

/-- Encode a clause `∀ xs, p₁ → … → pₙ → head`: its variables become constants, its premises
separate assertions, and its head is asserted negated. Premises that cannot be encoded are
omitted, which marks the encoding abstracted. Returns the premises and the head. -/
partial def encodeClause (clause : Expr) (premises : Array String := #[])
    : EncodeM (Array String × String) := do
  match (← instantiateMVars clause).consumeMData with
  | .forallE name domain body bi =>
    if ← isProp domain then
      if body.hasLooseBVar 0 then unsupported m!"proof-dependent premise"
      let premises ← try pure (premises.push (← withPolarity .pos (encode domain)))
        catch error =>
          if error.isInterrupt then throw error
          trace[flex.smt] "omitted premise: {error.toMessageData}"
          markAbstracted
          pure premises
      encodeClause (body.lowerLooseBVars 1 1) premises
    else
      -- A variable of an unencodable, possibly empty, type could make the clause vacuous.
      discard <| encodeSort domain
      withLocalDecl name bi domain fun x => encodeClause (body.instantiate1 x) premises
  | head => return (premises, ← withPolarity .neg (encode head))

initialize registerTraceClass `flex.smt

/-- Conjuncts of a proposition, for independent premise encoding. -/
partial def conjuncts (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then conjuncts (e.getArg! 0) ++ conjuncts (e.getArg! 1) else #[e]

/-- An encoded Horn clause `∀ binders, premises → head`. -/
structure HornClause where
  /-- `(symbol sort)` pairs. -/
  binders : Array String
  premises : Array String
  head : String
  deriving Inhabited

/-- Render as one `assert`: nested implications, or with `conjoined` one `and` of premises. -/
def HornClause.render (clause : HornClause) (conjoined : Bool := false) : String :=
  let body :=
    if clause.premises.isEmpty then clause.head
    else if conjoined then
      let guard := if clause.premises.size == 1 then clause.premises[0]!
        else s!"(and {" ".intercalate clause.premises.toList})"
      s!"(=> {guard} {clause.head})"
    else clause.premises.foldr (fun p body => s!"(=> {p} {body})") clause.head
  let body := if clause.binders.isEmpty then body
    else s!"(forall ({" ".intercalate clause.binders.toList}) {body})"
  s!"(assert {body})"

/-- Encode a clause `∀ xs, p₁ → … → pₙ → head` as a Horn clause, with `Config.horn` set and κs
bound in `Context.relations`. Variables become universal binders (`Nat` ones guarded by
`0 ≤ x`). A premise conjunct that cannot be encoded is dropped, which only strengthens the
clause, so any solution of the encoding still solves the original; it marks the encoding
abstracted. The head must encode. -/
partial def encodeHornClause (clause : Expr) : EncodeM HornClause :=
  go clause #[] #[]
where
  go (clause : Expr) (binders premises : Array String) : EncodeM HornClause := do
    match (← instantiateMVars clause).consumeMData with
    | .forallE name domain body bi =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then unsupported m!"proof-dependent premise"
        let mut premises := premises
        for conjunct in conjuncts domain do
          try premises := premises.push (← withPolarity .both (encode conjunct))
          catch error =>
            if error.isInterrupt || error.isRuntime then throw error
            trace[flex.smt] "omitted premise: {error.toMessageData}"
            markAbstracted
        go (body.lowerLooseBVars 1 1) binders premises
      else
        let sort ← encodeSort domain
        let nat ← isNatType domain
        withLocalDecl name bi domain fun x => do
          let symbol ← fresh name.toString
          let premises := if nat then premises.push s!"(>= {symbol} 0)" else premises
          withBinder x symbol <|
            go (body.instantiate1 x) (binders.push s!"({symbol} {sort})") premises
    | head => return { binders, premises, head := ← withPolarity .both (encode head) }

/-- Run an encoding, starting from an empty state. -/
def EncodeM.run' (config : Config) (k : EncodeM α) : MetaM α := do
  let (result, _) ← (k.run { config }).run {}
  return result

end Flex.SMT

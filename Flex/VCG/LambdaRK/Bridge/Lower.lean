import Flex.VCG.LambdaRK.Bridge.Syntax
import Flex.VCG.LambdaRK.Signature

/-!
An executable, deliberately untrusted scalarizer. Constructor equalities in
antecedents supply aliases; declared measure equations turn known constructors
into arithmetic. Observations of an arbitrary runtime value are introduced only
by a positive antecedent which supplies evaluation evidence. A consequent may
reuse those observations, but cannot assume an arbitrary measure is total.

Every proposed clause is checked separately by the proof-producing adapter.
Unsupported consequents retain their original source clause as a residual VC.
-/
namespace LambdaRK.Bridge

/-- Accumulating flattening preserves the original scope and guard order. -/
def flattenAux (constraint : Cstr) (frames : List SourceFrame)
    (path : List Nat) (next : Nat) : List SourceClause × Nat :=
  match constraint with
  | .truth => ([⟨next, path, frames, .theory .truth⟩], next + 1)
  | .head atom => ([⟨next, path, frames, atom⟩], next + 1)
  | .all name sort body => flattenAux body (frames ++ [.all name sort]) (path ++ [2]) next
  | .guard atom body => flattenAux body (frames ++ [.guard atom]) (path ++ [2]) next
  | .conj left right =>
      let (leftClauses, afterLeft) := flattenAux left frames (path ++ [0]) next
      let (rightClauses, afterRight) := flattenAux right frames (path ++ [1]) afterLeft
      (leftClauses ++ rightClauses, afterRight)

/-- Preserve exact source contexts, including administrative `True` leaves. -/
def flatten (constraint : Cstr) : Array SourceClause :=
  (flattenAux constraint [] [] 0).1.toArray

private structure CompilerState where
  binders : List (String × LSort)
  aliases : List (String × LTerm) := []
  variables : Array ScalarVariable := #[]
  guards : Array ScalarFormula := #[]
  dropped : Array String := #[]

private abbrev CompileM := StateT CompilerState (Except String)

/-- Fuel also bounds alias normalization for malformed or adversarial input.
No source-variable names are used as scalar variable identities. -/
private def normalize (aliases : List (String × LTerm)) : Nat → LTerm → Except String LTerm
  | 0, _ => .error "constructor aliases exceed the normalization limit"
  | fuel + 1, .var name => match aliases.lookup name with
      | some term => normalize aliases fuel term
      | none => .ok (.var name)
  | _ + 1, .int n => .ok (.int n)
  | _ + 1, .bool b => .ok (.bool b)
  | fuel + 1, .add left right => do
      return .add (← normalize aliases fuel left) (← normalize aliases fuel right)
  | fuel + 1, .ctor name fields => do
      return .ctor name (← fields.mapM (normalize aliases fuel))
  | fuel + 1, .measure name argument => do
      return .measure name (← normalize aliases fuel argument)

private def normalized (term : LTerm) : CompileM LTerm := do
  match normalize (← get).aliases 512 term with
  | .ok term => pure term
  | .error reason => throw reason

private def addAlias (name : String) (replacement : LTerm) : CompileM Unit := do
  if ((← get).aliases.lookup name).isSome then return
  let replacement ← normalized replacement
  -- An occurs check prevents recursive rewriting even in inconsistent guards
  -- such as `xs = cons x xs`. Such guards remain in the checked source clause.
  unless replacement.freeVars.contains name do
    modify fun state => { state with aliases := (name, replacement) :: state.aliases }

private def collectFormulaAliases : Formula → CompileM Unit
  | .eq (.var name) replacement => addAlias name replacement
  | .eq replacement (.var name) => addAlias name replacement
  | .and left right => do collectFormulaAliases left; collectFormulaAliases right
  | _ => pure ()

private def collectAliases : Atom → CompileM Unit
  | .theory formula => collectFormulaAliases formula
  | .kvar _ _ => pure ()

private def observation (term : LTerm) : CompileM (Option ScalarVariable) :=
  return (← get).variables.find? (fun scalar => scalar.observation == term)

private def recordObservation (term : LTerm) (sort : ScalarSort) : CompileM ScalarTerm := do
  if let some previous ← observation term then
    unless previous.sort == sort do
      throw s!"one observation is required at both scalar sorts: {repr term}"
    return .var previous.index sort
  let index := (← get).variables.size
  modify fun state => { state with variables := state.variables.push ⟨index, sort, term⟩ }
  return .var index sort

private def inferSort (term : LTerm) : CompileM (Option ScalarSort) := do
  let term ← normalized term
  match term with
  | .int _ | .add _ _ | .measure _ _ => return some .int
  | .bool _ => return some .bool
  | .ctor _ _ => return none
  | .var name =>
      if let some existing ← observation term then return some existing.sort
      return ((← get).binders.lookup name).bind ScalarSort.ofLogical

private def checkSort (actual expected : ScalarSort) : CompileM Unit :=
  unless actual == expected do throw "inconsistent integer/Boolean scalar sorts"

mutual
  /-- `fresh` is permitted only when the positive source antecedent supplies
  evaluation witnesses. Quantifiers of scalar sort supply their own witness. -/
  private def lowerTerm (signature : Signature) (fuel : Nat) (fresh : Bool)
      (expected : ScalarSort) (term : LTerm) : CompileM ScalarTerm := do
    match fuel with
    | 0 => throw "measure expansion exceeds the normalization limit"
    | fuel + 1 =>
      let term ← normalized term
      match term with
      | .int n => checkSort .int expected; return .int n
      | .bool b => checkSort .bool expected; return .bool b
      | .add left right =>
          checkSort .int expected
          return .add (← lowerTerm signature fuel fresh .int left)
            (← lowerTerm signature fuel fresh .int right)
      | .var name =>
          if let some previous ← observation term then
            checkSort previous.sort expected
            return .var previous.index previous.sort
          if let some sort := ((← get).binders.lookup name).bind ScalarSort.ofLogical then
            checkSort sort expected
            return ← recordObservation term sort
          if fresh then return ← recordObservation term expected
          throw s!"head needs an undefined scalar observation of {name}"
      | .ctor name _ => throw s!"constructor {name} is not a scalar term"
      | .measure name argument =>
          checkSort .int expected
          if let some previous ← observation term then return .var previous.index .int
          match argument with
          | .ctor constructor fields =>
              let some declaration := signature.findMeasure name
                | throw s!"unknown measure {name}"
              let some branch := declaration.cases.find? (fun branch => branch.ctor == constructor)
                | throw s!"measure {name} has no equation for constructor {constructor}"
              lowerMeasureBody signature fuel fresh name fields branch.body
          | _ =>
              if fresh then return ← recordObservation term .int
              throw s!"head needs measure {name} without evaluation evidence from a guard"

  private def lowerMeasureBody (signature : Signature) (fuel : Nat) (fresh : Bool)
      (name : String) (fields : List LTerm) (body : MeasureBody) : CompileM ScalarTerm := do
    match fuel with
    | 0 => throw "measure body exceeds the normalization limit"
    | fuel + 1 =>
      match body with
      | .literal n => return .int n
      | .field index =>
          let some field := fields[index]?
            | throw s!"measure {name} references missing field {index}"
          lowerTerm signature fuel fresh .int field
      | .recur index =>
          let some field := fields[index]?
            | throw s!"measure {name} recurses on missing field {index}"
          lowerTerm signature fuel fresh .int (.measure name field)
      | .add left right =>
          return .add (← lowerMeasureBody signature fuel fresh name fields left)
            (← lowerMeasureBody signature fuel fresh name fields right)
end

private def lowerFormula (signature : Signature) (fresh : Bool) :
    Formula → CompileM ScalarFormula
  | .truth => pure .truth
  | .falsity => pure .falsity
  | .eq left right => do
      let some sort := (← inferSort left).or (← inferSort right)
        | throw "equality of unencoded runtime values"
      return .eq (← lowerTerm signature 512 fresh sort left)
        (← lowerTerm signature 512 fresh sort right)
  | .le left right => do
      return .le (← lowerTerm signature 512 fresh .int left)
        (← lowerTerm signature 512 fresh .int right)
  | .and left right => do
      return .and (← lowerFormula signature fresh left) (← lowerFormula signature fresh right)
  | .or left right => do
      -- A disjunction does not provide either branch's evaluation witnesses.
      return .or (← lowerFormula signature false left) (← lowerFormula signature false right)
  | .not body => do
      -- Undefined logical terms make a negated formula true. Arithmetic
      -- negation is sound only when all of its observations already exist.
      return .not (← lowerFormula signature false body)

private def lowerAtom (signature : Signature) (fresh : Bool) : Atom → CompileM ScalarFormula
  | .theory formula => lowerFormula signature fresh formula
  | .kvar name arguments => do
      let some declaration := signature.findKVar name
        | throw s!"undeclared predicate {name}"
      unless declaration.args.length == arguments.length do
        throw s!"predicate {name} is applied at the wrong arity"
      if declaration.args.contains .value then
        throw s!"predicate {name} has an unsupported runtime-value argument"
      if (signature.kvars.filter (fun declaration => declaration.name == name)).length != 1 then
        throw s!"predicate {name} has an ambiguous declaration"
      let arguments ← (arguments.zip declaration.args).mapM fun (argument, sort) => do
        let some scalarSort := ScalarSort.ofLogical sort
          | throw s!"predicate {name} has a non-scalar argument"
        lowerTerm signature 512 fresh scalarSort argument
      return .rel name arguments

private def addGuard (signature : Signature) (atom : Atom) : CompileM Unit := do
  -- Process positive conjunctions individually. A rejected sibling must not
  -- erase useful evaluation evidence obtained from the other conjunct.
  match atom with
  | .theory (.and left right) =>
      addGuard signature (.theory left)
      addGuard signature (.theory right)
  | _ =>
      try
        let guard ← lowerAtom signature true atom
        modify fun state => { state with guards := state.guards.push guard }
      catch reason =>
        -- StateT over Except restores the state before the failed attempt.
        -- In particular a rejected disjunction cannot leak observations.
        modify fun state => { state with dropped := state.dropped.push reason }
termination_by atom

private def checkScopes : List SourceFrame → List String → Except String Unit
  | [], _ => .ok ()
  | .all name _ :: frames, used => do
      if used.contains name then
        throw s!"logical binder {name} shadows an earlier binder or guard variable"
      checkScopes frames (name :: used)
  | .guard atom :: frames, used => checkScopes frames (atom.freeVars ++ used)

/-- Propose one scalar clause. Its source context remains available even if
lowering fails, allowing the adapter to leave exactly that obligation behind. -/
def lowerClause (signature : Signature) (source : SourceClause) : Except String ScalarClause := do
  checkScopes source.frames []
  let action : CompileM ScalarFormula := do
    source.guards.forM collectAliases
    source.guards.forM (addGuard signature)
    lowerAtom signature false source.head
  let (head, state) ← action.run { binders := source.binders }
  return {
    source := source
    variables := state.variables
    guards := state.guards
    head := head
    droppedGuards := state.dropped
  }

/-- Compile all leaves independently. No solver call and no proof assertion is
made here; the adapter must certify each `.ok` proposal against its source. -/
def lower (signature : Signature) (constraint : Cstr) : Lowering :=
  { relations := (signature.kvars.filter (fun declaration => !declaration.args.contains .value)).toArray
    clauses := (flatten constraint).map fun source => ⟨source, lowerClause signature source⟩ }

end LambdaRK.Bridge

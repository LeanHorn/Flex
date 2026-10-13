import Flex.VCG.SystemFRK.Judgments
import Flex.VCG.SystemFRK.Binding.AlphaEquivalence

/-! Bidirectional checking and Horn constraint generation. Dependent arguments
are ANF observations; datatype parameters are invariant. Predicate signatures are explicit. -/
namespace SystemFRK

def Cstr.andThen (left right : Cstr) : Cstr :=
  match left, right with
  | .truth, c | c, .truth => c
  | _, _ => .conj left right

def guardPredicates (predicates : List Atom) (body : Cstr) : Cstr :=
  predicates.foldr Cstr.guard body

/-- A declared measure is defined on values of its datatype. These positive
self-equalities carry evaluation witnesses through the first-order VC. -/
def typeFacts (signature : Signature) (ty : Ty) (term : LTerm) : List Atom :=
  match ty.outerBase with
  | .data family _ => signature.measures.flatMap fun measure =>
      match signature.findMeasure measure.name with
      | some declaration =>
        if declaration.datatype == family then
          [.theory (.eq (.measure measure.name term) (.measure measure.name term))]
        else []
      | none => []
  | _ => []

def bindConstraint (signature : Signature) (name : String) (ty : Ty) (body : Cstr) : Cstr :=
  .all name ty.sort (guardPredicates (typeFacts signature ty (.var name))
    (guardPredicates (ty.outerPredicates.map (Atom.substTerm valueName (.var name))) body))

def bindFields (signature : Signature) (fields : List (String × Ty)) (body : Cstr) : Cstr :=
  fields.foldr (fun (name, ty) c => bindConstraint signature name ty c) body

def failUnless (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

abbrev GenM := StateT Nat (Except String)

/-- Check a constructor's field telescope in source order. Kept separate from
the expression recursion so its state and typing invariants have a direct
structural induction. -/
def checkFieldsWith (checkField : Expr → Ty → GenM Cstr) :
    List Expr → List Ty → GenM Cstr
  | [], [] => pure .truth
  | field :: fields, type :: types => do
    let head ← checkField field type
    let tail ← checkFieldsWith checkField fields types
    return head.andThen tail
  | _, _ => throw "constructor field telescope has the wrong length"

def fresh : GenM String := do
  let n ← get
  set (n + 1)
  return s!"$g{n}"

/-- Keep the usual generated name when possible, and avoid capture even when
subtyping is called on types containing generated logical names. -/
def freshAvoid (avoid : List String) : GenM String := do
  let candidate ← fresh
  return if (valueName :: avoid).contains candidate then
    freshTermName candidate (valueName :: avoid) else candidate

/-- Observations used in dependent application may not refer to the reserved
refinement witness. Source variables satisfy this check. -/
def observeFresh (expression : Expr) : Except String LTerm := do
  let term ← observe expression
  failUnless (!term.freeVars.contains valueName) "observation captures the refinement witness"
  return term

/-- Check structural scope at recursive checker boundaries. -/
def checkScope (context : Context) (type : Ty) : Except String Unit :=
  failUnless (type.scopeCheck context) "inferred or expected type escapes its context"

/-- Attach the outer refinement implication to a structural subtype constraint. -/
def finishSubtype (source target : Ty) (structural : Cstr) : GenM Cstr := do
  if target.outerPredicates.isEmpty then return structural
  let witness ← freshAvoid (source.allTermNames ++ target.allTermNames)
  let assumptions := source.outerPredicates.map (Atom.substTerm valueName (.var witness))
  let goals := target.outerPredicates.map fun p =>
    Cstr.head (Atom.substTerm valueName (.var witness) p)
  return structural.andThen (.all witness source.sort
    (guardPredicates assumptions (goals.foldr Cstr.andThen .truth)))

/-- Finish a synthesis branch with complete result formation. Kept as a
separate computation so an early `return` cannot bypass the certificate. -/
def finishSynth (signature : Signature) (context : Context) (output : Cstr × Ty) : GenM (Cstr × Ty) := do
  wfTy signature context 512 output.2
  return output

/-- Structural subtyping plus Horn obligations for the outer refinements.
Datatype parameters are invariant modulo alpha-equivalence. -/
def subtype (sig : Signature) (ctx : Context) : Nat → Ty → Ty → GenM Cstr
  | 0, _, _ => throw "subtyping exceeds the checker depth limit"
  | fuel + 1, source, target => do
    let baseSource := source.outerBase
    let baseTarget := target.outerBase
    let structural ← match baseSource, baseTarget with
      | .int, .int | .bool, .bool => pure Cstr.truth
      | .var i, .var j =>
        failUnless (i == j) "different type variables"
        pure Cstr.truth
      | .data a args, .data b args' =>
        failUnless ((Ty.data a args).alphaEq 512 (.data b args')) "datatype type arguments do not match"
        pure Cstr.truth
      | .arrow x a b, .arrow y a' b' =>
        let pre ← subtype sig ctx fuel a' a
        let name ← freshAvoid (source.allTermNames ++ target.allTermNames)
        let next := { ctx with vars := (name, a') :: ctx.vars }
        let post ← subtype sig next fuel
          (Ty.substTerm x (.var name) b) (Ty.substTerm y (.var name) b')
        pure (pre.andThen (bindConstraint sig name a' post))
      | .all body, .all body' => subtype sig ctx.underType fuel body body'
      | _, _ => throw "source and expected type have different shapes"
    finishSubtype source target structural

/-- Check each pattern branch with a supplied recursive body checker. The
shared context operations are also used by the independent typing rules. -/
def checkBranchesWith (signature : Signature) (checkBody : Context → Expr → Ty → GenM Cstr)
    (context : Context) (scrutinee : String) (data : DataDecl) (arguments : List Ty)
    (expected : Ty) : List (String × List String × Expr) → GenM Cstr
  | [] => pure .truth
  | (name, names, body) :: rest => do
    let some ctor := data.ctors.find? (fun ctor => ctor.name == name)
      | throw s!"constructor '{name}' does not belong to '{data.name}'"
    failUnless (names.length == ctor.fields.length) "pattern has the wrong number of fields"
    let fields := names.zip (ctor.fields.map (Ty.instantiateParams arguments))
    let next ← extendFields context fields
    let bodyC ← checkBody (markSmaller next scrutinee fields) body expected
    let restC ← checkBranchesWith signature checkBody context scrutinee data arguments expected rest
    let equation := Atom.theory (.eq (.var scrutinee) (.ctor name (names.map LTerm.var)))
    return (bindFields signature fields (.guard equation bodyC)).andThen restC

mutual
  /-- Fuel-indexed synthesis. The public equations support executable-generator
  correctness proofs without unfolding the mutual recursion implementation. -/
  def synthFuel (sig : Signature) (ctx : Context) : Nat → Expr → GenM (Cstr × Ty)
    | 0, _ => throw "expression exceeds the checker depth limit"
    | fuel + 1, expression => do
      match expression with
      | .var name =>
        let some ty := ctx.vars.lookup name | throw s!"unbound term variable '{name}'"
        finishSynth sig ctx (.truth, selfType name ty)
      | .int n => finishSynth sig ctx (.truth, .refine .int (.theory (.eq (.var valueName) (.int n))))
      | .bool b => finishSynth sig ctx (.truth, .refine .bool (.theory (.eq (.var valueName) (.bool b))))
      | .ann e ty =>
        wfTy sig ctx 512 ty
        let c ← checkFuel sig ctx fuel e ty
        finishSynth sig ctx (c, ty)
      | .lam name domain body =>
        wfTy sig ctx 512 domain
        let next ← ctx.add name domain
        let (c, result) ← synthFuel sig next fuel body
        finishSynth sig ctx (bindConstraint sig name domain c, .arrow name domain result)
      | .tyLam body =>
        let (c, ty) ← synthFuel sig ctx.underType fuel body
        finishSynth sig ctx (c, .all ty)
      | .tyApp function argument =>
        wfTy sig ctx 512 argument
        let (c, ty) ← synthFuel sig ctx fuel function
        let .all body := ty.outerBase | throw "type application expects a polymorphic function"
        finishSynth sig ctx (c, Ty.substType argument 0 body)
      | .app function argument =>
        let observation ← observeFresh argument
        let (c, ty) ← synthFuel sig ctx fuel function
        let .arrow name domain result := ty.outerBase | throw "application expects a function"
        let pre ← checkFuel sig ctx fuel argument domain
        finishSynth sig ctx (c.andThen pre, Ty.substTerm name observation result)
      | .letE name value body =>
        let (c, ty) ← synthFuel sig ctx fuel value
        let next ← ctx.add name ty
        let (d, result) ← synthFuel sig next fuel body
        -- A synthesized result must not retain a local name that has gone out
        -- of scope. Annotate the let expression when it needs such elimination.
        failUnless (!(result.freeVars.contains name))
          "inferred let result escapes its local binder; add an outer type annotation"
        finishSynth sig ctx (c.andThen (bindConstraint sig name ty d), result)
      | .ctor name arguments fields =>
        let some (data, ctor) := sig.findCtor name | throw s!"unknown constructor '{name}'"
        failUnless (arguments.length == data.params) s!"constructor '{name}' has wrong type arity"
        let _ ← (arguments.forM (fun argument => do
          wfTy sig ctx 512 argument
          pure PUnit.unit) : Except String PUnit)
        failUnless (fields.length == ctor.fields.length) s!"constructor '{name}' has wrong field arity"
        let c ← checkFieldsWith (checkFuel sig ctx fuel) fields
          (ctor.fields.map (Ty.instantiateParams arguments))
        let observed ← (fields.mapM observe : Except String (List LTerm))
        finishSynth sig ctx (c, .refine (.data data.name arguments)
          (.theory (.eq (.var valueName) (.ctor name observed))))
      | .structRec name domain result body =>
        wfTy sig ctx 512 domain
        let .data _ _ := domain.outerBase | throw "structural recursion requires a datatype argument"
        let next ← ctx.add name domain
        wfTy sig next 512 result
        let next := { next with recursion := some { binder := name, domain, codomain := result }
                                smaller := [] }
        let c ← checkFuel sig next fuel body result
        finishSynth sig ctx (bindConstraint sig name domain c, .arrow name domain result)
      | .recur argument =>
        let some recursion := ctx.recursion | throw "recursive call outside structural recursion"
        let .var name := argument | throw "recursive argument must be a smaller pattern variable"
        failUnless (ctx.smaller.contains name) "recursive call is not on a structurally smaller field"
        let c ← checkFuel sig ctx fuel argument recursion.domain
        finishSynth sig ctx (c, Ty.substTerm recursion.binder (.var name) recursion.codomain)
      | .measure name argument =>
        let observed ← observe argument
        let (c, ty) ← synthFuel sig ctx fuel argument
        let some measure := sig.findMeasure name | throw s!"unknown measure '{name}'"
        let .data data _ := ty.outerBase | throw "measure argument must have a datatype type"
        failUnless (data == measure.datatype) s!"measure '{name}' has the wrong argument datatype"
        finishSynth sig ctx (c, .refine .int (.theory (.eq (.var valueName) (.measure name observed))))
      | .matchE _ _ => throw "pattern matching needs an expected result type or annotation"

  /-- Fuel-indexed checking, exposed alongside `synthFuel` for equation proofs. -/
  def checkFuel (sig : Signature) (ctx : Context) : Nat → Expr → Ty → GenM Cstr
    | 0, _, _ => throw "expression exceeds the checker depth limit"
    | fuel + 1, expression, expected => do
      wfTy sig ctx 512 expected
      match expression, expected.outerBase with
      | .lam name domain body, .arrow binder targetDomain result =>
        wfTy sig ctx 512 domain
        -- Check annotation compatibility while retaining the expected refinement.
        let pre ← subtype sig ctx fuel targetDomain domain
        wfTy sig ctx 512 targetDomain
        let next ← ctx.add name targetDomain
        let c ← checkFuel sig next fuel body (Ty.substTerm binder (.var name) result)
        wfTy sig ctx 512 (.arrow name targetDomain (Ty.substTerm binder (.var name) result))
        failUnless expected.outerPredicates.isEmpty "annotate a function value before refining it"
        return pre.andThen (bindConstraint sig name targetDomain c)
      | .tyLam body, .all result =>
        failUnless expected.outerPredicates.isEmpty "refined polymorphic introductions need an annotation"
        checkFuel sig ctx.underType fuel body result
      | .letE name value body, _ =>
        let (c, ty) ← synthFuel sig ctx fuel value
        let next ← ctx.add name ty
        let d ← checkFuel sig next fuel body expected
        return c.andThen (bindConstraint sig name ty d)
      | .matchE scrutinee branches, _ =>
        let .var scrutineeName := scrutinee | throw "match scrutinee must be a let-bound variable"
        let (scrutineeC, scrutineeTy) ← synthFuel sig ctx fuel scrutinee
        let .data name arguments := scrutineeTy.outerBase | throw "match expects a datatype"
        let some data := sig.findData name | throw s!"unknown datatype '{name}'"
        let names := branches.map (·.1)
        failUnless (names.length == data.ctors.length && names.eraseDups.length == names.length &&
          data.ctors.all (fun ctor => names.contains ctor.name))
          "match must cover every constructor exactly once"
        let branchesC ← checkBranchesWith sig (checkFuel sig · fuel) ctx scrutineeName
          data arguments expected branches
        return scrutineeC.andThen branchesC
      | _, _ =>
        let (c, actual) ← synthFuel sig ctx fuel expression
        let d ← subtype sig ctx fuel actual expected
        return c.andThen d
end

def synth (sig : Signature) (ctx : Context) (expression : Expr) : Except String (Cstr × Ty) :=
  (synthFuel sig ctx 1024 expression).run' 0

def check (sig : Signature) (ctx : Context) (expression : Expr) (expected : Ty) : Except String Cstr := do
  wfTy sig ctx 512 expected
  (checkFuel sig ctx 1024 expression expected).run' 0

/-- Check a closed program and return its Horn constraints. -/
def generate (sig : Signature) (expression : Expr) (expected : Ty) : Except String Cstr := do
  sig.validate
  for data in sig.datatypes do
    for ctor in data.ctors do
      for field in ctor.fields do
        wfTy sig { typeDepth := data.params } 512 field
  check sig {} expression expected

end SystemFRK

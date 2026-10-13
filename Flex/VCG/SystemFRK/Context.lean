import Flex.VCG.SystemFRK.Signature

/-! Executable context and type-formation checks. Source binders are fresh;
`$` names are reserved for generated witnesses. -/
namespace SystemFRK

structure RecScope where
  binder : String
  domain : Ty
  codomain : Ty
  deriving Repr, Inhabited

structure Context where
  typeDepth : Nat := 0
  vars : List (String × Ty) := []
  recursion : Option RecScope := none
  smaller : List String := []
  deriving Repr, Inhabited

def Context.names (context : Context) : List String := context.vars.map Prod.fst

/-- Structural formation, independent of the bounded executable checker. -/
def Ty.InScope (type : Ty) (context : Context) : Prop :=
  type.TypeScoped context.typeDepth ∧
    ∀ name ∈ type.freeVars, name ∈ context.names

def Ty.outerBase : Ty → Ty
  | .refine t _ => t.outerBase
  | t => t

def Ty.outerPredicates : Ty → List Atom
  | .refine t p => t.outerPredicates ++ [p]
  | _ => []

def Context.underType (ctx : Context) : Context :=
  { ctx with typeDepth := ctx.typeDepth + 1
             vars := ctx.vars.map fun (x, t) => (x, Ty.shiftTypes 1 0 t)
             recursion := ctx.recursion.map fun r =>
               { r with domain := Ty.shiftTypes 1 0 r.domain
                        codomain := Ty.shiftTypes 1 0 r.codomain } }

private def failUnless (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def Context.add (ctx : Context) (name : String) (ty : Ty) : Except String Context := do
  failUnless (!name.isEmpty && !name.startsWith "$")
    s!"invalid or reserved term binder '{name}'"
  failUnless (!(ctx.vars.any fun entry => entry.1 == name))
    s!"term binder '{name}' shadows an existing variable"
  return { ctx with vars := (name, ty) :: ctx.vars }

theorem Context.add_eq_ok (ctx next : Context) (name : String) (ty : Ty) :
    ctx.add name ty = .ok next ↔
      name.isEmpty = false ∧ name.startsWith "$" = false ∧
      name ∉ ctx.names ∧ next = { ctx with vars := (name, ty) :: ctx.vars } := by
  simp [Context.add, failUnless, Context.names]
  split <;> simp_all [Except.bind, Except.map, bind, Functor.map]
  split <;> simp_all
  all_goals grind

/-- Abstract type variables retain their identity in logical equality. Treating
all of them as the same erased Value sort is not stable under instantiation. -/
private def abstractKind (ty : Ty) : Option Nat :=
  match ty.outerBase with
  | .var index => some index
  | _ => none

private def logicKind (ty : Ty) : LSort × Option String :=
  match ty.outerBase with
  | .data name _ => (.value, some name)
  | _ => (ty.sort, none)

private def inferLogic (sig : Signature) (ctx : Context) :
    Nat → LTerm → Except String (LSort × Option String)
  | 0, _ => .error "logical term exceeds the checker depth limit"
  | fuel + 1, term => do
    match term with
    | .var name =>
      let some ty := ctx.vars.lookup name | throw s!"unbound logical variable '{name}'"
      return logicKind ty
    | .int _ => return (.int, none)
    | .bool _ => return (.bool, none)
    | .add a b =>
      failUnless ((← inferLogic sig ctx fuel a).1 == .int &&
        (← inferLogic sig ctx fuel b).1 == .int) "addition requires integer terms"
      return (.int, none)
    | .ctor name fields =>
      let some (data, ctor) := sig.findCtor name | throw s!"unknown constructor '{name}'"
      failUnless (fields.length == ctor.fields.length) s!"constructor '{name}' has wrong arity"
      for field in fields, expected in ctor.fields do
        let actual ← inferLogic sig ctx fuel field
        failUnless (expected.sort == .value || actual.1 == expected.sort)
          s!"ill-sorted field of '{name}'"
        if let .data family _ := expected.outerBase then
          failUnless (actual.2 == some family)
            s!"field of '{name}' expects datatype '{family}'"
      return (.value, some data.name)
    | .measure name argument =>
      let some measure := sig.findMeasure name | throw s!"unknown measure '{name}'"
      let actual ← inferLogic sig ctx fuel argument
      failUnless (actual.2 == some measure.datatype)
        s!"measure '{name}' expects '{measure.datatype}'"
      return (.int, none)

private def abstractTermKind (ctx : Context) : LTerm → Option Nat
  | .var name => (ctx.vars.lookup name).bind abstractKind
  | _ => none

private def wfFormula (sig : Signature) (ctx : Context) : Nat → Formula → Except String Unit
  | 0, _ => .error "formula exceeds the checker depth limit"
  | fuel + 1, formula => do
    match formula with
    | .truth | .falsity => pure ()
    | .eq a b =>
      let ka ← inferLogic sig ctx fuel a
      let kb ← inferLogic sig ctx fuel b
      failUnless (abstractTermKind ctx a == abstractTermKind ctx b)
        "equality compares incompatible abstract types"
      failUnless (ka.1 == kb.1) "equality compares different logical sorts"
      if let some da := ka.2 then
        if let some db := kb.2 then
          failUnless (da == db) "equality compares different datatypes"
    | .le a b =>
      failUnless ((← inferLogic sig ctx fuel a).1 == .int &&
        (← inferLogic sig ctx fuel b).1 == .int) "comparison requires integer terms"
    | .and a b | .or a b => wfFormula sig ctx fuel a; wfFormula sig ctx fuel b
    | .not a => wfFormula sig ctx fuel a

def wfAtom (sig : Signature) (ctx : Context) (atom : Atom) : Except String Unit := do
  match atom with
  | .theory formula => wfFormula sig ctx 512 formula
  | .kvar name arguments =>
    let some decl := sig.findKVar name | throw s!"undeclared predicate '{name}'"
    failUnless (decl.args.length == arguments.length) s!"predicate '{name}' has wrong arity"
    for arg in arguments, expected in decl.args do
      let actual ← inferLogic sig ctx 512 arg
      failUnless (expected == .value || actual.1 == expected)
        s!"predicate '{name}' has an argument of the wrong sort"

private def checkAllTypes (check : Ty → Except String Unit) : List Ty → Except String Unit
  | [] => .ok ()
  | type :: types => do check type; checkAllTypes check types

/-- Fuel-bounded formation checker; the public entry point also certifies scope. -/
private def wfTyCore (sig : Signature) (ctx : Context) : Nat → Ty → Except String Unit
  | 0, _ => .error "type exceeds the checker depth limit"
  | fuel + 1, ty => do
    match ty with
    | .int | .bool => pure ()
    | .var index => failUnless (index < ctx.typeDepth) s!"unbound type variable {index}"
    | .data name arguments =>
      let some decl := sig.findData name | throw s!"unknown datatype '{name}'"
      failUnless (arguments.length == decl.params) s!"datatype '{name}' has wrong arity"
      checkAllTypes (wfTyCore sig ctx fuel) arguments
    | .arrow name domain codomain =>
      wfTyCore sig ctx fuel domain
      -- Type binders have lexical scope. They may reuse an outer term name;
      -- only expression binders use Context.add's no-shadowing restriction.
      failUnless (!name.isEmpty && !name.startsWith "$")
        s!"invalid or reserved type binder '{name}'"
      wfTyCore sig { ctx with vars := (name, domain) :: ctx.vars } fuel codomain
    | .all body => wfTyCore sig ctx.underType fuel body
    | .refine base predicate =>
      wfTyCore sig ctx fuel base
      wfAtom sig { ctx with vars := (valueName, base) :: ctx.vars } predicate

/-- Check type indices and free logical names against the context. -/
def Ty.scopeCheck (type : Ty) (context : Context) : Bool :=
  type.indicesScoped context.typeDepth && type.freeVars.all context.names.contains

theorem Ty.scopeCheck_eq_true (type : Ty) (context : Context) :
    type.scopeCheck context = true ↔ type.InScope context := by
  simp [Ty.scopeCheck, Ty.InScope, Ty.indicesScoped_eq_true]

/-- Check formation, then certify structural scope once. -/
def wfTy (sig : Signature) (ctx : Context) (fuel : Nat) (type : Ty) : Except String Unit := do
  wfTyCore sig ctx fuel type
  failUnless (type.scopeCheck ctx) "type contains an out-of-scope index or logical name"

theorem wfTy_inScope (signature : Signature) (context : Context) (type : Ty)
    (fuel : Nat) (formed : wfTy signature context fuel type = .ok ()) :
    type.InScope context := by
  apply (type.scopeCheck_eq_true context).mp
  cases checked : wfTyCore signature context fuel type with
  | error message => simp [wfTy, checked, bind, Except.bind] at formed
  | ok result =>
    simp only [wfTy, checked, bind, Except.bind, failUnless] at formed
    split at formed
    · assumption
    · contradiction

private theorem unit_bind_ok (action : Except String Unit)
    (next : Unit → Except String Unit) :
    action >>= next = .ok () ↔ action = .ok () ∧ next () = .ok () := by
  cases action with
  | error message => simp [bind, Except.bind]
  | ok result => cases result; simp [bind, Except.bind]

private theorem checkAllTypes_mono (left right : Ty → Except String Unit)
    (includes : ∀ type, left type = .ok () → right type = .ok ())
    (types : List Ty) (formed : checkAllTypes left types = .ok ()) :
    checkAllTypes right types = .ok () := by
  induction types with
  | nil => rfl
  | cons type types ih =>
    simp only [checkAllTypes, unit_bind_ok] at formed ⊢
    exact ⟨includes type formed.1, ih formed.2⟩

private theorem wfTyCore_mono (sig : Signature) (ctx : Context) (type : Ty)
    (fuel more : Nat) (bound : fuel ≤ more)
    (formed : wfTyCore sig ctx fuel type = .ok ()) :
    wfTyCore sig ctx more type = .ok () := by
  induction fuel generalizing ctx type more with
  | zero => simp [wfTyCore] at formed
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      have bound : fuel ≤ more := by omega
      cases type with
      | var | int | bool => exact formed
      | all body => exact ih ctx.underType body more bound formed
      | refine base predicate =>
        simp only [wfTyCore, unit_bind_ok] at formed ⊢
        exact ⟨ih ctx base more bound formed.1, formed.2⟩
      | data name arguments =>
        cases found : sig.findData name with
        | none => simp [wfTyCore, found] at formed
        | some decl =>
          simp only [wfTyCore, found, unit_bind_ok] at formed ⊢
          exact ⟨formed.1, checkAllTypes_mono _ _ (fun t => ih ctx t more bound) _ formed.2⟩
      | arrow name domain codomain =>
        simp only [wfTyCore, unit_bind_ok] at formed ⊢
        exact ⟨ih ctx domain more bound formed.1, formed.2.1,
          ih _ codomain more bound formed.2.2⟩

private theorem wfTyCore_outerBase (sig : Signature) (ctx : Context) (type : Ty)
    (fuel : Nat) (formed : wfTyCore sig ctx fuel type = .ok ()) :
    wfTyCore sig ctx fuel type.outerBase = .ok () := by
  induction fuel generalizing type with
  | zero => simp [wfTyCore] at formed
  | succ fuel ih =>
    cases type with
    | refine base predicate =>
      simp only [wfTyCore, unit_bind_ok] at formed
      exact wfTyCore_mono sig ctx base.outerBase fuel (fuel + 1) (by omega) (ih base formed.1)
    | _ => exact formed

/-- Removing outer refinements preserves the complete formation check. -/
theorem wfTy_outerBase (sig : Signature) (ctx : Context) (type : Ty) (fuel : Nat)
    (formed : wfTy sig ctx fuel type = .ok ()) :
    wfTy sig ctx fuel type.outerBase = .ok () := by
  have hasScope := wfTy_inScope sig ctx type fuel formed
  have baseScoped : type.outerBase.InScope ctx := by
    clear formed
    induction type using Ty.rec (motive_2 := fun _ => True) with
    | refine base predicate ih =>
      apply ih
      exact ⟨by simpa only [Ty.TypeScoped] using hasScope.1,
        fun n hn => hasScope.2 n (by simp [Ty.freeVars, hn])⟩
    | nil | cons => trivial
    | _ => exact hasScope
  simp only [wfTy, unit_bind_ok] at formed ⊢
  refine ⟨wfTyCore_outerBase sig ctx type fuel formed.1, ?_⟩
  simp [failUnless, (type.outerBase.scopeCheck_eq_true ctx).mpr baseScoped]

def selfType (name : String) (ty : Ty) : Ty :=
  .refine ty (.theory (.eq (.var valueName) (.var name)))

/-- Logical expressions are observations of already evaluated ANF values. -/
def observe : Expr → Except String LTerm
  | .var name => .ok (.var name)
  | .int n => .ok (.int n)
  | .bool b => .ok (.bool b)
  | _ => .error "use a let-bound variable for this dependent argument"

end SystemFRK

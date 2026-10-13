import Flex.VCG.LambdaRK.Syntax

/-! Executable binding operations. Type substitution removes one type binder;
parameter instantiation substitutes a whole datatype telescope simultaneously.
Named term binders are freshened before substitutions to prevent capture. -/

namespace LambdaRK

def LTerm.substTerm (term : LTerm) (name : String) (replacement : LTerm) : LTerm :=
  match term with
  | .var x => if x == name then replacement else .var x
  | .int n => .int n
  | .bool b => .bool b
  | .add a b => .add (a.substTerm name replacement) (b.substTerm name replacement)
  | .ctor c args => .ctor c (args.map (·.substTerm name replacement))
  | .measure m a => .measure m (a.substTerm name replacement)

def LTerm.freeVars : LTerm → List String
  | .var x => [x]
  | .int _ | .bool _ => []
  | .add a b => a.freeVars ++ b.freeVars
  | .ctor _ args => args.flatMap LTerm.freeVars
  | .measure _ a => a.freeVars

def Formula.substTerm (name : String) (replacement : LTerm) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .eq a b => .eq (a.substTerm name replacement) (b.substTerm name replacement)
  | .le a b => .le (a.substTerm name replacement) (b.substTerm name replacement)
  | .and a b => .and (a.substTerm name replacement) (b.substTerm name replacement)
  | .or a b => .or (a.substTerm name replacement) (b.substTerm name replacement)
  | .not a => .not (a.substTerm name replacement)

def Formula.freeVars : Formula → List String
  | .truth | .falsity => []
  | .eq a b | .le a b => a.freeVars ++ b.freeVars
  | .and a b | .or a b => a.freeVars ++ b.freeVars
  | .not a => a.freeVars

def Atom.substTerm (name : String) (replacement : LTerm) : Atom → Atom
  | .theory f => .theory (f.substTerm name replacement)
  | .kvar k args => .kvar k (args.map (·.substTerm name replacement))

def Atom.freeVars : Atom → List String
  | .theory f => f.freeVars
  | .kvar _ args => args.flatMap LTerm.freeVars

/-- Transform free type indices, passing the number of crossed type binders. -/
def Ty.mapTypes (f : Nat → Nat → Ty) (depth : Nat) : Ty → Ty
  | .var i => f depth i
  | .int => .int
  | .bool => .bool
  | .data n args => .data n (args.map (·.mapTypes f depth))
  | .arrow x a b => .arrow x (a.mapTypes f depth) (b.mapTypes f depth)
  | .all a => .all (a.mapTypes f (depth + 1))
  | .refine a p => .refine (a.mapTypes f depth) p

def Ty.shiftTypes (amount cutoff : Nat) (ty : Ty) : Ty :=
  ty.mapTypes (fun depth i => .var (if cutoff + depth ≤ i then i + amount else i)) 0

/-- Substitute a free logical variable. `$value` is bound by each refinement. -/
def Ty.substTermRaw (name : String) (replacement : LTerm) : Ty → Ty
  | .var i => .var i
  | .int => .int
  | .bool => .bool
  | .data n args => .data n (args.map (·.substTermRaw name replacement))
  | .arrow x a b => .arrow x (a.substTermRaw name replacement)
      (if x == name then b else b.substTermRaw name replacement)
  | .all a => .all (a.substTermRaw name replacement)
  | .refine a p => .refine (a.substTermRaw name replacement)
      (if name == valueName then p else p.substTerm name replacement)

def Ty.stripRefinements : Ty → Ty
  | .var i => .var i
  | .int => .int
  | .bool => .bool
  | .data n args => .data n (args.map Ty.stripRefinements)
  | .arrow x a b => .arrow x a.stripRefinements b.stripRefinements
  | .all a => .all a.stripRefinements
  | .refine a _ => a.stripRefinements

/-- Erased solver-facing sort; `value` is intentionally not an SMT encoding. -/
def Ty.sort : Ty → LSort
  | .int => .int
  | .bool => .bool
  | .refine a _ => a.sort
  | _ => .value

def Ty.freeVars : Ty → List String
  | .var _ | .int | .bool => []
  | .data _ args => args.flatMap Ty.freeVars
  | .arrow x a b => a.freeVars ++ b.freeVars.filter (· != x)
  | .all a => a.freeVars
  | .refine a p => a.freeVars ++ p.freeVars.filter (· != valueName)

/-- All logical names, including bound names, used when choosing fresh binders. -/
def Ty.allTermNames : Ty → List String
  | .var _ | .int | .bool => []
  | .data _ args => args.flatMap Ty.allTermNames
  | .arrow x a b => x :: (a.allTermNames ++ b.allTermNames)
  | .all a => a.allTermNames
  | .refine a p => a.allTermNames ++ p.freeVars

def freshTermName (base : String) (avoid : List String) : String :=
  let candidates := (List.range (avoid.length + 1)).map (fun n => s!"{base}_{n}")
  match candidates.find? (fun name => !avoid.contains name) with
  | some name => name
  | none =>
    -- There are more distinct candidates than forbidden names. This fallback
    -- also stays fresh without depending on that cardinality proof.
    String.ofList (List.replicate
      ((avoid.map String.length).foldl max 0 + 1) 'x')

def LTerm.renameNames (renames : List (String × String)) : LTerm → LTerm
  | .var x => .var ((renames.lookup x).getD x)
  | .int n => .int n
  | .bool b => .bool b
  | .add a b => .add (a.renameNames renames) (b.renameNames renames)
  | .ctor n args => .ctor n (args.map (·.renameNames renames))
  | .measure n a => .measure n (a.renameNames renames)

def Formula.renameNames (renames : List (String × String)) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .eq a b => .eq (a.renameNames renames) (b.renameNames renames)
  | .le a b => .le (a.renameNames renames) (b.renameNames renames)
  | .and a b => .and (a.renameNames renames) (b.renameNames renames)
  | .or a b => .or (a.renameNames renames) (b.renameNames renames)
  | .not a => .not (a.renameNames renames)

def Atom.renameNames (renames : List (String × String)) : Atom → Atom
  | .theory p => .theory (p.renameNames renames)
  | .kvar n args => .kvar n (args.map (·.renameNames renames))

/-- Internal traversal exposed for structural binding proofs. -/
def Ty.freshenBindersAux (avoid : List String)
    (renames : List (String × String)) : Ty → Ty
  | .var i => .var i
  | .int => .int
  | .bool => .bool
  | .data n args => .data n (args.map (·.freshenBindersAux avoid renames))
  | .arrow x a b =>
    let next := if avoid.contains x then
      freshTermName x (avoid ++ a.allTermNames ++ b.allTermNames) else x
    .arrow next (a.freshenBindersAux avoid renames)
      (b.freshenBindersAux (next :: avoid) ((x, next) :: renames))
  | .all a => .all (a.freshenBindersAux avoid renames)
  | .refine a p => .refine (a.freshenBindersAux avoid renames)
      (p.renameNames (renames.filter (fun entry => entry.1 != valueName)))

/-- Alpha-rename arrow binders away from forbidden names and one another.
The fixed refinement witness is always reserved. Free logical names remain
unchanged, including uses of `$value` outside refinement predicates. -/
def Ty.freshenBinders (avoid : List String) (ty : Ty) : Ty :=
  ty.freshenBindersAux (valueName :: avoid ++ ty.freeVars) []

/-- Capture-avoiding substitution of a free logical variable. -/
def Ty.substTerm (name : String) (replacement : LTerm) (ty : Ty) : Ty :=
  (ty.freshenBinders replacement.freeVars).substTermRaw name replacement

/-- Capture-avoiding substitution for index `index`, decrementing indices above
it. Type binders use shifting; named term binders are alpha-renamed when a type
argument carries free logical names or its own dependent function binders. -/
def Ty.substType (replacement : Ty) (index : Nat) (ty : Ty) : Ty :=
  let replacement := replacement.freshenBinders ty.allTermNames
  let ty := ty.freshenBinders replacement.allTermNames
  ty.mapTypes (fun depth i =>
    if i == index + depth then replacement.shiftTypes depth 0
    else .var (if index + depth < i then i - 1 else i)) 0

/-- Instantiate datatype parameters simultaneously, avoiding capture of the
arguments' logical names. Parameters are numbered in declaration order. -/
def Ty.instantiateParams (args : List Ty) (ty : Ty) : Ty :=
  let args := args.map (·.freshenBinders ty.allTermNames)
  let ty := ty.freshenBinders (args.flatMap Ty.allTermNames)
  ty.mapTypes (fun depth i =>
    if i < depth then .var i
    else match args[i - depth]? with
      | some replacement => replacement.shiftTypes depth 0
      | none => .var (i - args.length)) 0

/-- Apply a type operation throughout an expression, tracking type binders. -/
def Expr.mapTypes (f : Nat → Ty → Ty) (depth : Nat) : Expr → Expr
  | .var x => .var x
  | .int n => .int n
  | .bool b => .bool b
  | .lam x a e => .lam x (f depth a) (e.mapTypes f depth)
  | .app e a => .app (e.mapTypes f depth) (a.mapTypes f depth)
  | .letE x e body => .letE x (e.mapTypes f depth) (body.mapTypes f depth)
  | .tyLam e => .tyLam (e.mapTypes f (depth + 1))
  | .tyApp e a => .tyApp (e.mapTypes f depth) (f depth a)
  | .ctor c args fields => .ctor c (args.map (f depth))
      (fields.map (·.mapTypes f depth))
  | .matchE e branches => .matchE (e.mapTypes f depth)
      (branches.attach.map fun ⟨(c, xs, body), _⟩ => (c, xs, body.mapTypes f depth))
  | .structRec x a b e => .structRec x (f depth a) (f depth b) (e.mapTypes f depth)
  | .recur e => .recur (e.mapTypes f depth)
  | .measure m e => .measure m (e.mapTypes f depth)
  | .ann e a => .ann (e.mapTypes f depth) (f depth a)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- Substitute in expression annotations, for logically closed replacements.
This helper tracks type binders but does not rename expression term binders.
The evaluator erases type arguments and does not use this operation. -/
def Expr.substType (replacement : Ty) (index : Nat) (expr : Expr) : Expr :=
  expr.mapTypes (fun depth ty => Ty.substType (replacement.shiftTypes depth 0)
    (index + depth) ty) 0

def Expr.shiftTypes (amount cutoff : Nat) (expr : Expr) : Expr :=
  expr.mapTypes (fun depth ty => ty.shiftTypes amount (cutoff + depth)) 0

/-- Free term names, including names occurring in type annotations. -/
def Expr.freeVars : Expr → List String
  | .var x => [x]
  | .int _ | .bool _ => []
  | .lam x a e => a.freeVars ++ e.freeVars.filter (· != x)
  | .app e a => e.freeVars ++ a.freeVars
  | .letE x e body => e.freeVars ++ body.freeVars.filter (· != x)
  | .tyLam e => e.freeVars
  | .tyApp e a => e.freeVars ++ a.freeVars
  | .ctor _ args fields => args.flatMap Ty.freeVars ++ fields.flatMap Expr.freeVars
  | .matchE e branches => e.freeVars ++ branches.attach.flatMap
      (fun ⟨(_, xs, body), _⟩ => body.freeVars.filter (fun x => !xs.contains x))
  | .structRec x a b e => a.freeVars ++
      b.freeVars.filter (· != x) ++ e.freeVars.filter (· != x)
  | .recur e | .measure _ e => e.freeVars
  | .ann e a => e.freeVars ++ a.freeVars
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)

end LambdaRK

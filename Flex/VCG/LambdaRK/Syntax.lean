import Lean

/-!
# The draft λRK language

This frontend deliberately keeps its syntax separate from the existing STLC
frontend. Terms have named binders (the checker rejects shadowing); type binders
use de Bruijn indices. `$value` denotes the value being refined and is reserved.
The language has explicit System F polymorphism, positive datatypes, structural
recursion, and total integer-valued measures. It has no unrestricted fixpoint.
-/

namespace LambdaRK

abbrev valueName : String := "$value"

inductive LSort where
  | int | bool | value
  deriving BEq, Repr, Inhabited, DecidableEq

inductive LTerm where
  | var (name : String)
  | int (value : Int)
  | bool (value : Bool)
  | add (left right : LTerm)
  | ctor (name : String) (fields : List LTerm)
  | measure (name : String) (argument : LTerm)
  deriving Repr, Inhabited

/-- Structural equality must reduce in the kernel: Lean's derived `BEq` for
nested inductives is opaque, which prevents proofs about checker results. -/
def LTerm.equal : LTerm → LTerm → Bool
  | .var x, .var y => x == y
  | .int x, .int y => x == y
  | .bool x, .bool y => x == y
  | .add a b, .add c d => a.equal c && b.equal d
  | .ctor x fields, .ctor y others =>
      x == y && fields.length == others.length &&
        ((fields.map fun field => field.equal).zip others).all (fun (compare, other) => compare other)
  | .measure x a, .measure y b => x == y && a.equal b
  | _, _ => false

instance : BEq LTerm := ⟨LTerm.equal⟩

inductive Formula where
  | truth | falsity
  | eq (left right : LTerm)
  | le (left right : LTerm)
  | and (left right : Formula)
  | or (left right : Formula)
  | not (body : Formula)
  deriving BEq, Repr, Inhabited

inductive Atom where
  | theory (formula : Formula)
  | kvar (name : String) (arguments : List LTerm)
  deriving BEq, Repr, Inhabited

inductive Ty where
  | var (index : Nat)
  | int | bool
  | data (name : String) (arguments : List Ty)
  | arrow (binder : String) (domain codomain : Ty)
  | all (body : Ty)
  | refine (base : Ty) (predicate : Atom)
  deriving Repr, Inhabited

/-- Kernel-reducible equality for the other nested syntax inspected by `generate`.
Mapping the recursive comparators first makes structural descent explicit. -/
def Ty.equal : Ty → Ty → Bool
  | .var x, .var y => x == y
  | .int, .int | .bool, .bool => true
  | .data x arguments, .data y others =>
      x == y && arguments.length == others.length &&
        ((arguments.map fun argument => argument.equal).zip others).all
          (fun (compare, other) => compare other)
  | .arrow x a b, .arrow y c d => x == y && a.equal c && b.equal d
  | .all a, .all b => a.equal b
  | .refine a p, .refine b q => a.equal b && p == q
  | _, _ => false

instance : BEq Ty := ⟨Ty.equal⟩

inductive Expr where
  | var (name : String)
  | int (value : Int)
  | bool (value : Bool)
  | lam (binder : String) (domain : Ty) (body : Expr)
  | app (function argument : Expr)
  | letE (binder : String) (value body : Expr)
  | tyLam (body : Expr)
  | tyApp (function : Expr) (argument : Ty)
  | ctor (name : String) (typeArguments : List Ty) (fields : List Expr)
  | matchE (scrutinee : Expr) (branches : List (String × List String × Expr))
  /-- `structRec x A B body` is a function structurally recursive on the ADT argument
  `x : A`; `recur` may only be applied to a certified smaller pattern variable. -/
  | structRec (binder : String) (domain codomain : Ty) (body : Expr)
  | recur (argument : Expr)
  | measure (name : String) (argument : Expr)
  | ann (expression : Expr) (type : Ty)
  deriving BEq, Repr, Inhabited

structure CtorDecl where
  name : String
  fields : List Ty
  deriving BEq, Repr, Inhabited

structure DataDecl where
  name : String
  params : Nat
  ctors : List CtorDecl
  deriving BEq, Repr, Inhabited

/-- Measure programs cannot call arbitrary source-language functions. Recursive
calls specify a direct recursive field of the current constructor. -/
inductive MeasureBody where
  | literal (value : Int)
  | field (index : Nat)
  | recur (index : Nat)
  | add (left right : MeasureBody)
  deriving BEq, Repr, Inhabited

structure MeasureCase where
  ctor : String
  body : MeasureBody
  deriving BEq, Repr, Inhabited

structure MeasureDecl where
  name : String
  datatype : String
  cases : List MeasureCase
  deriving BEq, Repr, Inhabited

structure KDecl where
  name : String
  args : List LSort
  deriving BEq, Repr, Inhabited

structure Signature where
  datatypes : List DataDecl := []
  measures : List MeasureDecl := []
  kvars : List KDecl := []
  deriving BEq, Repr, Inhabited

/-- Constraints retain typed quantifiers and predicate applications. A later
solver adapter may lower a supported fragment; this syntax is not an SMT AST. -/
inductive Cstr where
  | truth
  | head (atom : Atom)
  | guard (antecedent : Atom) (consequent : Cstr)
  | all (binder : String) (sort : LSort) (body : Cstr)
  | conj (left right : Cstr)
  deriving BEq, Repr, Inhabited

end LambdaRK

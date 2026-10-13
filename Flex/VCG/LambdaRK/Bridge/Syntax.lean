import Flex.VCG.LambdaRK.Syntax

/-!
The executable scalar frontend has its own small syntax. It deliberately keeps
source clauses and scalar observations: the proof-producing adapter checks each
proposed lowering against the source semantics before using a solver witness.
-/
namespace LambdaRK.Bridge

inductive ScalarSort where
  | int | bool
  deriving BEq, DecidableEq, Repr, Inhabited

def ScalarSort.ofLogical : LSort → Option ScalarSort
  | .int => some .int
  | .bool => some .bool
  | .value => none

inductive ScalarTerm where
  | var (index : Nat) (sort : ScalarSort)
  | int (value : Int)
  | bool (value : Bool)
  | add (left right : ScalarTerm)
  deriving Repr, Inhabited

def ScalarTerm.sort : ScalarTerm → ScalarSort
  | .var _ sort => sort
  | .int _ | .add _ _ => .int
  | .bool _ => .bool

inductive ScalarFormula where
  | truth | falsity
  | eq (left right : ScalarTerm)
  | le (left right : ScalarTerm)
  | and (left right : ScalarFormula)
  | or (left right : ScalarFormula)
  | not (body : ScalarFormula)
  | rel (name : String) (arguments : List ScalarTerm)
  deriving Repr, Inhabited

/-- Scalar variables have fresh numeric identities, independent of source names.
`observation` records the evaluation evidence needed by the checked bridge. -/
structure ScalarVariable where
  index : Nat
  sort : ScalarSort
  observation : LTerm
  deriving Repr, Inhabited

inductive SourceFrame where
  | all (name : String) (sort : LSort)
  | guard (atom : Atom)
  deriving Repr, Inhabited

def SourceFrame.wrap : SourceFrame → Cstr → Cstr
  | .all name sort, body => .all name sort body
  | .guard atom, body => .guard atom body

def wrapFrames (frames : List SourceFrame) (body : Cstr) : Cstr :=
  frames.foldr SourceFrame.wrap body

/-- A leaf and its exact quantifier/guard context. `path` uses 0/1 for the two
conjuncts and 2 for a quantifier or guard body; it is diagnostic provenance. -/
structure SourceClause where
  index : Nat
  path : List Nat
  frames : List SourceFrame
  head : Atom
  deriving Repr, Inhabited

def SourceClause.constraint (source : SourceClause) : Cstr :=
  wrapFrames source.frames (.head source.head)

def SourceClause.binders (source : SourceClause) : List (String × LSort) :=
  source.frames.filterMap fun frame => match frame with
    | .all name sort => some (name, sort)
    | .guard _ => none

def SourceClause.guards (source : SourceClause) : List Atom :=
  source.frames.filterMap fun frame => match frame with
    | .all _ _ => none
    | .guard atom => some atom

structure ScalarClause where
  source : SourceClause
  variables : Array ScalarVariable
  guards : Array ScalarFormula
  head : ScalarFormula
  /-- Untranslated antecedents were dropped, strengthening the scalar clause.
  Their original source propositions remain available to the checked bridge. -/
  droppedGuards : Array String := #[]
  deriving Repr, Inhabited

structure LoweredClause where
  source : SourceClause
  result : Except String ScalarClause
  deriving Repr, Inhabited

structure Lowering where
  relations : Array KDecl
  clauses : Array LoweredClause
  deriving Repr, Inhabited

def Lowering.supported (lowering : Lowering) : Array ScalarClause :=
  lowering.clauses.filterMap fun clause => match clause.result with
    | .ok scalar => some scalar
    | .error _ => none

def Lowering.diagnostics (lowering : Lowering) : Array (Nat × String) :=
  lowering.clauses.filterMap fun clause => match clause.result with
    | .ok _ => none
    | .error message => some (clause.source.index, message)

end LambdaRK.Bridge

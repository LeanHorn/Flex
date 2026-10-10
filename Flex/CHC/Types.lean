import Flex.Core.KVar
import Smt.Translate.Commands

namespace Flex.CHC

/-- The first exporter supports SMT integers and Booleans. -/
inductive ValueSort where
  | int | bool
  deriving BEq, Repr, Inhabited

def ValueSort.toTerm : ValueSort → Smt.Term
  | .int => .symbolT "Int"
  | .bool => .symbolT "Bool"

/-- Stable correspondence between a solver symbol and an existing Flex witness slot.
`leanType` distinguishes Lean `Bool` from `Prop`, although both encode as SMT Bool.
Argument positions include unused parameters. No temporary local variables escape. -/
structure Relation where
  symbol : String
  kvar : KVar
  leanType : Lean.Expr
  argumentSorts : Array ValueSort
  deriving Inhabited

def Relation.smtType (relation : Relation) : Smt.Term :=
  relation.argumentSorts.foldr (fun sort rest => .arrowT sort.toTerm rest) (.symbolT "Bool")

/-- A checked CHC script and the correspondence needed to import its model later.
Commands assert the original constraints, ending in `check-sat`. Model requests
and solver-specific options belong to the process runner. -/
structure ExportedProblem where
  relations : Array Relation
  commands : List Smt.Translate.Command
  clauseCount : Nat
  deriving Inhabited

end Flex.CHC

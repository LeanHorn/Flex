import Lean
import Std
import Flex.Core.KVar

open Lean List Meta

/-!
  # κ-Variable Context

  - `KContext` tracks which `MVarId`s are κ-variables during `Expr` traversal.
  - `KM` is a reader monad over `MetaM` carrying this context.
-/
structure KContext where
  kvars : Std.HashMap MVarId KVar

abbrev KM := ReaderT KContext MetaM

def KM.getKVar? (id : MVarId) : KM (Option KVar) :=
  (·.kvars.get? id) <$> read

def KM.getKVarList : KM (List KVar) :=
  (·.kvars.values) <$> read

-- `isKApp` checks if an expression `e` is `κ` application.
def KM.isKApp (e : Expr) : KM (Option (KVar × Array Expr)) := do
  let fn := e.getAppFn
  if fn.isMVar then
    if let some κ ← KM.getKVar? fn.mvarId! then
      return some (κ, e.getAppArgs)
  return none

/-
  Equivalent to e.constainsFVar, but custom addition
  checks if an Expr contains reference to MVar or not
  it instantiatesMVar e first to ensure possible mvars
  are resolved.
-/
def Lean.Expr.containsMVar (e : Expr) (mvarId : MVarId) : Bool :=
  e.hasMVar && (e.find? fun sub => sub.isMVar && sub.mvarId! == mvarId).isSome

/-
  Collect all κ-variables referenced in an Expr,
  filter KVars in the context based on whether they
  are in the `e : Expr`, returning the filtered list.
-/
def KM.exprKVars (e : Expr) : KM (List KVar) := do
  let kvars ← KM.getKVarList
  return kvars.filter fun κ => e.containsMVar κ.mvarId

/-- The κ at the head of the flat clause `fc`, found under its outer `∀`s
    (unfolding definitions to expose them). `none` if the head is not a κ. -/
def findHeadKVar (fc : Expr) : KM (Option KVar) :=
  forallTelescopeReducing fc (whnfType := true) fun _ head => do
    return (← KM.isKApp head).map (·.1)

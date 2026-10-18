import Lean

open Lean Meta

initialize qualifAttr : TagAttribute ←
  registerTagAttribute `qualif "Marks a definition as a PA qualifier."

/-- Collect local and imported definitions tagged `@[qualif]`. -/
def getQualifiers : MetaM (Array Expr) := do
  let s := qualifAttr.ext.toEnvExtension.getState (← getEnv)
  let mut names : NameSet := s.state
  for moduleEntries in s.importedEntries do
    for name in moduleEntries do
      names := names.insert name
  names.toArray.mapM fun n => mkConstWithLevelParams n

/-- Apply arguments and unfold the qualifier, keeping relations like `≤` readable. -/
def Expr.instQualifier (q : Expr) (args : Array Expr) : MetaM Expr := do
  let applied := mkAppN q args
  match ← unfoldDefinition? applied with
  | some unfolded => return unfolded.headBeta
  | none          => return applied.headBeta

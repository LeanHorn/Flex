import Flex.Fusion.Flatten
import Flex.CHC.Prepare
import Flex.CHC.Script
import Smt.Translate.Query
import Smt2Lean.Chc

namespace Flex.CHC

open Lean Meta

private def relation (kvar : KVar) (index : Nat) : MetaM Relation := do
  if ← kvar.mvarId.isAssigned then
    throwError "CHC export: predicate '{kvar.name}' is already assigned"
  let type ← instantiateMVars (← kvar.mvarId.getType)
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelMVar then
    throwError "CHC export: predicate '{kvar.name}' has an open or unresolved signature"
  let sorts ← forallTelescopeReducing type fun parameters result => do
    unless result.isProp do
      throwError "CHC export: predicate '{kvar.name}' must return Prop"
    unless parameters.size == kvar.paramTypes.length && parameters.size == kvar.params.length do
      throwError "CHC export: parameter metadata disagrees with predicate '{kvar.name}'"
    parameters.mapIdxM fun i parameter => do
      let parameterType ← inferType parameter
      if parameterType.hasFVar then
        throwError "CHC export: dependent predicate parameters are unsupported"
      unless ← isDefEq parameterType kvar.paramTypes[i]! do
        throwError "CHC export: parameter {i + 1} has inconsistent metadata for '{kvar.name}'"
      Fragment.valueSort parameterType
  return { symbol := s!"k_{index}", kvar, leanType := type, argumentSorts := sorts }

private def validate (problem : ExportedProblem) : MetaM Unit := do
  (Smt2Lean.Chc.parseAndInspectProblem problem.toSMTLib (name := "flex-chc") fun parsed => do
    unless parsed.constants.isEmpty && parsed.functions.isEmpty &&
        parsed.relations.size == problem.relations.size && parsed.clauses.size == problem.clauseCount do
      throw (.error "CHC export: unexpected declarations or clause count after validation")
    for expected in problem.relations do
      let some actual := parsed.relations.find? (·.name == expected.symbol)
        | throw (.error s!"CHC export: missing relation '{expected.symbol}'")
      unless actual.argumentSorts.size == expected.argumentSorts.size do
        throw (.error s!"CHC export: wrong arity for '{expected.symbol}'")
      for actualSort in actual.argumentSorts, expectedSort in expected.argumentSorts do
        unless (match expectedSort with | .int => actualSort.isInteger | .bool => actualSort.isBoolean) do
          throw (.error s!"CHC export: wrong argument sort for '{expected.symbol}'")
  ).runIO

/-- Export an already peeled Flex body and its κs in existential order.

The body must be closed except for these unassigned κ metavariables. Ambient
parameters/assumptions are not silently declared or asserted: put the required
value binders and guards in the body. The initial fragment is first-order
Bool/Int Horn constraints with linear arithmetic, standard operator instances,
and local lets. Unsupported terms fail before any solver can run.

This function does not peel a goal, assign witnesses, or prove constraints. It
restores the caller's meta state and translator registrations on success/error.
Only the supplied κ identities, closed signature metadata, and SMT commands escape.
-/
def exportConstraints (kvars : List KVar) (body : Expr) : MetaM ExportedProblem := do
  let saved ← Meta.saveState
  try
    Fragment.withTranslators do
      let mut seen : Std.HashSet MVarId := {}
      for kvar in kvars do
        if seen.contains kvar.mvarId then throwError "CHC export: duplicate κ identity '{kvar.name}'"
        seen := seen.insert kvar.mvarId
      let relations ← kvars.toArray.mapIdxM fun i kvar => relation kvar i
      let body ← instantiateMVars body
      if body.hasFVar then
        throwError "CHC export: free local variables in the body; bind parameters and guards explicitly"
      if body.hasLooseBVars then throwError "CHC export: loose bound variable in the body"
      unless ← isProp body do throwError "CHC export: expected a proposition"
      let context : KContext := { kvars := kvars.foldl (fun ctx k => ctx.insert k.mvarId k) {} }
      let clauses ← (exprFlat body Prepare.expose).run context
      withLocalDeclsDND (relations.map fun r => (.mkSimple r.symbol, r.leanType)) fun symbols => do
        let replacements := (relations.zip symbols).foldl
          (fun map (r, symbol) => map.insert r.kvar.mvarId symbol) ({} : Std.HashMap MVarId Expr)
        let names := (relations.zip symbols).foldl
          (fun map (r, symbol) => map.insert symbol.fvarId! r.symbol) ({} : Std.HashMap FVarId String)
        let clauses ← clauses.toArray.mapIdxM fun i original => do
          try
            let input := original.replace fun e => if e.isMVar then replacements[e.mvarId!]? else none
            if input.hasMVar then throwError "unregistered or unresolved metavariable"
            let clause ← Prepare.clause input
            let ((term, constants, freeVariables), _) ← (Smt.Translator.translateExpr clause).run {
              uniqueFVarNames := names }
            unless constants.isEmpty do
              throwError "unsupported constant dependencies: {constants.toArray}"
            unless freeVariables.toArray.all names.contains do
              throwError "unexpected free variable in translation"
            Fragment.checkTerm term (relations.map (·.symbol))
            return clause
          catch error => throwError "CHC export: clause {i + 1}: {error.toMessageData}"
        withLocalDeclsDND (clauses.mapIdx fun i c => (.mkSimple s!"clause_{i}", c)) fun hypotheses => do
          let commands ← Smt.Translate.Query.generateQuery (symbols ++ hypotheses).toList names
          let problem : ExportedProblem := {
            relations
            commands := [.setLogic "HORN"] ++ commands ++ [.checkSat]
            clauseCount := clauses.size }
          validate problem
          return problem
  finally saved.restore

end Flex.CHC

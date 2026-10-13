import Demo.SystemFRK
import Flex.VCG.SystemFRK.Bridge.Flatten

/-! Executable frontend regressions. These check fragment boundaries before any
solver runs; the bridge separately proves each accepted lowering in the kernel. -/
namespace SystemFRK.Bridge.Tests

-- The actual generated map has three substantive clauses and one True leaf.
#guard match Examples.mapVC with
  | .error _ => false
  | .ok constraints =>
      let result := lower Examples.signature constraints
      result.diagnostics.isEmpty && result.supported.size == 4

private def length (name : String) : LTerm := .measure "len" (.var name)

private def unguarded : Cstr := .all "xs" .value
  (.head (.kvar "mapLength" [length "xs", .int 0]))

-- Measures are partial on arbitrary runtime values.
#guard (lower Examples.signature unguarded).supported.isEmpty

-- A disjunction or negation does not establish that its observed value exists.
#guard (lower Examples.signature
  (.all "xs" .value (.guard (.theory (.or (.eq (length "xs") (.int 0)) .truth))
    (.head (.kvar "mapLength" [length "xs", .int 0]))))).supported.isEmpty
#guard (lower Examples.signature
  (.all "xs" .value (.guard (.theory (.not (.eq (length "xs") (.int 0))))
    (.head (.kvar "mapLength" [length "xs", .int 0]))))).supported.isEmpty

private def mixed : Signature :=
  { kvars := [{ name := "mixed", args := [.bool, .int] }] }

private def mixedClause : Cstr := .all "flag" .bool (.all "n" .int
  (.guard (.kvar "mixed" [.var "flag", .var "n"])
    (.head (.kvar "mixed" [.var "flag", .add (.var "n") (.int 1)]))))

#guard match (lower mixed mixedClause).supported.toList with
  | [clause] => clause.variables.toList.map (·.sort) == [.bool, .int]
  | _ => false

-- Measure fields and recursion work for independently named declarations.
private def weighted : Signature := {
  datatypes := [{
    name := "Chain"
    params := 0
    ctors := [{ name := "end", fields := [] },
      { name := "link", fields := [.int, .data "Chain" []] }]
  }]
  measures := [{
    name := "weight"
    datatype := "Chain"
    cases := [{ ctor := "end", body := .literal 0 },
      { ctor := "link", body := .add (.field 0) (.recur 1) }]
  }]
  kvars := [{ name := "weights", args := [.int] }]
}

private def weightedClause : Cstr := .all "n" .int (.all "tail" .value
  (.guard (.kvar "weights" [.measure "weight" (.var "tail")])
    (.head (.kvar "weights" [.measure "weight" (.ctor "link" [.var "n", .var "tail"])]))))

#guard match (lower weighted weightedClause).supported.toList with
  | [clause] => match clause.head with
      | .rel "weights" [.add (.var 1 .int) (.var 0 .int)] => true
      | _ => false
  | _ => false

-- Runtime-valued predicates and lexical shadowing remain source obligations.
#guard (lower { kvars := [{ name := "valuePredicate", args := [.value] }] }
  (.all "x" .value (.head (.kvar "valuePredicate" [.var "x"])))).supported.isEmpty
#guard (lower mixed (.all "n" .int mixedClause)).supported.isEmpty

run_elab do
  for theoremName in [``flatten_sound, ``flatten_valid_sound] do
    let axioms ← Lean.collectAxioms theoremName
    unless axioms.all (fun name => name == ``propext || name == ``Classical.choice ||
        name == ``Quot.sound) do
      throwError "source-clause assembly has a nonstandard axiom: {theoremName}: {axioms}"

end SystemFRK.Bridge.Tests

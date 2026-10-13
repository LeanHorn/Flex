import Flex.CHC.Types

namespace Flex.CHC

/-- Group a clause's universal prefix into one SMT binder list. lean-smt's AST
stores one binder per node; its default nested serialization makes Spacer's
preprocessing reject some mixed Bool/Int clauses. Generated names are distinct,
so merging this prefix preserves scope. Everything else uses the upstream printer. -/
private def clauseSexp (term : Smt.Term) : Sexp :=
  go term []
where
  go : Smt.Term → List Sexp → Sexp
    | .forallT name sort body, binders =>
      go body (.expr [.atom (Smt.Term.quoteSymbol name), ToSexp.toSexp sort] :: binders)
    | body, [] => ToSexp.toSexp body
    | body, binders => .expr [.atom "forall", .expr binders.reverse, ToSexp.toSexp body]

private def commandSexp : Smt.Translate.Command → Sexp
  | .assert term => .expr [.atom "assert", clauseSexp term]
  | command => ToSexp.toSexp command

/-- Render the checked script with grouped universal binders for both backends.
Runners should use this instead of printing `commands` individually. -/
def ExportedProblem.toSMTLib (problem : ExportedProblem) : String :=
  Sexp.serializeMany (problem.commands.map commandSexp) ++ "\n"

end Flex.CHC

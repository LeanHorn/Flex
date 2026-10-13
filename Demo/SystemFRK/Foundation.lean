import Flex.VCG.SystemFRK.Datatypes.Adequacy

/-! One model-construction stress test: positive recursive occurrences under
both function fields and polymorphic fields. This accompanies the two program
examples; it is not another frontend case study. -/
namespace SystemFRK.FoundationChecks

private def signature : Signature := {
  datatypes := [{ name := "Suspended", params := 1, ctors := [
    { name := "stop", fields := [] },
    { name := "function", fields := [.arrow "argument" .int (.data "Suspended" [.var 0])] },
    { name := "polymorphic", fields := [.all (.data "Suspended" [.var 1])] }
  ] }]
}

private theorem accepted : signature.validate = .ok () := by cbv

/-- The abstract adequacy premise now has a constructed witness even for
higher-order and polymorphic recursive fields. -/
theorem higherOrderModel (assignment : KAssignment) :
    DatatypeAdequate signature (signature.datatypeModel assignment) assignment :=
  signature.datatypeModel_adequate assignment accepted

end SystemFRK.FoundationChecks

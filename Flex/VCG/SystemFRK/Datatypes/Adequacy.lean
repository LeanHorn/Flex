import Flex.VCG.SystemFRK.Datatypes.Interpretation

/-! The constructed datatype model satisfies the constructor laws. -/
namespace SystemFRK

theorem Signature.datatypeModel_adequate (signature : Signature) (assignment : KAssignment)
    (accepted : signature.validate = .ok ()) :
    DatatypeAdequate signature (signature.datatypeModel assignment) assignment := by
  have ready := signature.validate_modelReady 256 accepted
  exact datatypeAdequate_of_constructor_laws signature (signature.datatypeModel assignment) assignment
    (Signature.modelReadyFrom_names [] signature.datatypes ready).1
    (Signature.modelReadyFrom_fields [] signature.datatypes ready)
    (signature.datatypeModel_laws assignment ready)

end SystemFRK

import Flex.VCG.LambdaRK.DatatypeInterpretation

/-! Adequacy of the constructed model for every accepted datatype signature.
No logical-relation assumption, termination assumption, or admitted interface
is used to install the model. -/
namespace LambdaRK

theorem Signature.datatypeModel_adequate (signature : Signature) (assignment : KAssignment)
    (accepted : signature.validate = .ok ()) :
    DatatypeAdequate signature (signature.datatypeModel assignment) assignment := by
  have ready := signature.validate_modelReady 256 accepted
  exact datatypeAdequate_of_constructor_laws signature (signature.datatypeModel assignment) assignment
    (Signature.modelReadyFrom_names [] signature.datatypes ready).1
    (Signature.modelReadyFrom_fields [] signature.datatypes ready)
    (signature.datatypeModel_laws assignment ready)

theorem datatype_model_exists (signature : Signature) (assignment : KAssignment)
    (accepted : signature.validate = .ok ()) :
    ∃ model : DataModel, DatatypeAdequate signature model assignment :=
  ⟨signature.datatypeModel assignment, signature.datatypeModel_adequate assignment accepted⟩

end LambdaRK

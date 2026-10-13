import Flex.VCG.SystemFRK.Generator.Soundness
import Flex.VCG.SystemFRK.Typing.Fundamental

/-! Successful generation and valid constraints imply total correctness. -/
namespace SystemFRK

theorem vcgen_total_correctness
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr)
    (adequate : DatatypeAdequate signature model assignment)
    (generated : generate signature expression type = .ok constraint)
    (satisfied : constraint.Valid signature assignment) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature model assignment [] [] value := by
  exact fundamental_closed signature model assignment (generate_checked generated).1 adequate
    expression type (checker_soundness signature model assignment expression type constraint
      generated satisfied)

/-- The canonical datatype interpretation discharges the model premise, leaving
only generator success and validity of its returned constraints. -/
theorem generated_total_correctness
    (signature : Signature) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr)
    (generated : generate signature expression type = .ok constraint)
    (satisfied : constraint.Valid signature assignment) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature (signature.datatypeModel assignment) assignment [] [] value :=
  vcgen_total_correctness signature (signature.datatypeModel assignment) assignment expression type
    constraint (signature.datatypeModel_adequate assignment (generate_checked generated).1)
    generated satisfied

end SystemFRK

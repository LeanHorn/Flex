import Flex.VCG.LambdaRK.DraftBinding
import Flex.VCG.LambdaRK.DraftCore
import Flex.VCG.LambdaRK.Judgments
import Flex.VCG.LambdaRK.VCGen
import Flex.VCG.LambdaRK.SemanticTyping
import Flex.VCG.LambdaRK.SemanticsLemmas
import Flex.VCG.LambdaRK.StructuralOrder
import Flex.VCG.LambdaRK.DatatypeAdequacy
import Flex.VCG.LambdaRK.DraftRecursion
import Flex.VCG.LambdaRK.Correctness

/-!
# Compatibility theorem names for the staged λRK development

The PR1–6 statements are now all proved. These wrappers retain their original
interfaces; the canonical proofs live in `MeasureLemmas`, `CheckerSoundness`,
`Fundamental`, and `Correctness`. There are no remaining admissions here.
-/

namespace LambdaRK.Draft

/-! Proved substitution interfaces are in `DraftBinding`. -/

/-- PR5: evaluation is deterministic, including captured recursion frames. -/
theorem evaluation_deterministic
    {signature : Signature} {environment : Environment} {frame : RecursionFrame}
    {expression : Expr} {left right : Value}
    (hleft : Eval signature environment frame expression left)
    (hright : Eval signature environment frame expression right) : left = right :=
  Eval.deterministic hleft hright

/-- PR5/10: logical measure observations have a unique result. -/
theorem measure_deterministic
    {signature : Signature} {name : String} {value : Value} {left right : Int}
    (hleft : MeasureEval signature name value left)
    (hright : MeasureEval signature name value right) : left = right :=
  MeasureEval.deterministic hleft hright

/-- PR8: constructor-field descent is well founded on runtime values. -/
theorem structural_order_wellFounded : WellFounded Smaller :=
  Smaller.wellFounded

/-- PR7: construct the positive datatype interpretation, rather than leaving
adequacy as an assumption of the final system. Signature validation checks
ordered declarations, regular parameters, and strict positivity. The proof
accounts for function and polymorphic fields as well as direct recursion. -/
theorem datatype_model_exists
    (signature : Signature) (assignment : KAssignment)
    (validSignature : signature.validate = .ok ()) :
    ∃ model : DataModel, DatatypeAdequate signature model assignment := by
  exact LambdaRK.datatype_model_exists signature assignment validSignature

/-- PR10: validated measures terminate on values of their declared datatype. -/
theorem measure_total
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (types : TypeEnvironment) (environment : Environment)
    (name : String) (declaration : MeasureDecl) (arguments : List Ty) (value : Value)
    (declared : signature.findMeasure name = some declaration)
    (typed : (Ty.data declaration.datatype arguments).denote
      signature model assignment types environment value) :
    ∃ result, MeasureEval signature name value result := by
  exact LambdaRK.measure_total signature model assignment validSignature adequate
    types environment name declaration arguments value declared typed

/-- PR11: semantic subtyping is transitive under the same context and facts. -/
theorem subtyping_transitive
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (context : Context) (assumptions : List Atom) (first middle last : Ty)
    (left : Subtype signature model assignment context assumptions first middle)
    (right : Subtype signature model assignment context assumptions middle last) :
    Subtype signature model assignment context assumptions first last := by
  intro types environment depth variables facts value typed
  exact right types environment depth variables facts value
    (left types environment depth variables facts value typed)

/-- PR11: the executable generator agrees with the independent declarative
rules once its actual generated constraints are satisfied. -/
theorem checker_soundness
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr)
    (_adequate : DatatypeAdequate signature model assignment)
    (generated : generate signature expression type = .ok constraint)
    (satisfied : constraint.Valid signature assignment) :
    HasType signature model assignment {} [] expression type := by
  exact LambdaRK.checker_soundness signature model assignment expression type constraint
    generated satisfied

/-- The open fundamental theorem introduced in PR4. `SemTyped` exposes static
scope, typed environments, branch assumptions, and a recursion-frame induction
hypothesis restricted to strict subvalues. PR6 establishes the System F cases;
constructor/match, measure, and recursion cases now complete the argument. -/
theorem fundamental_open
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (context : Context) (assumptions : List Atom) (expression : Expr) (type : Ty)
    (typed : HasType signature model assignment context assumptions expression type) :
    SemTyped signature model assignment context assumptions expression type := by
  exact LambdaRK.fundamental_open signature model assignment validSignature adequate
    context assumptions expression type typed

/-- Closed total correctness follows from the proved open fundamental theorem. -/
theorem fundamental_closed
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (expression : Expr) (type : Ty)
    (typed : HasType signature model assignment {} [] expression type) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature model assignment [] [] value := by
  exact SemTyped.closed
    (fundamental_open signature model assignment validSignature adequate {} [] expression type typed)

/-- PR12: desired end-to-end guarantee, conditional on an explicit adequate
model and satisfaction of the generated CHCs. This is total correctness, not
just a claim about executions that happen to terminate. -/
theorem vcgen_total_correctness
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (expression : Expr) (type : Ty) (constraint : Cstr)
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (generated : generate signature expression type = .ok constraint)
    (satisfied : constraint.Valid signature assignment) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature model assignment [] [] value := by
  exact fundamental_closed signature model assignment validSignature adequate expression type
    (checker_soundness signature model assignment expression type constraint adequate generated satisfied)

end LambdaRK.Draft

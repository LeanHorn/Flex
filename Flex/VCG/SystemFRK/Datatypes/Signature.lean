import Flex.VCG.SystemFRK.Binding.Formation

/-! Declaration lookup, constructor-tag uniqueness, and scoped field formation. -/
namespace SystemFRK

private theorem eq_of_nodup_map {α β : Type} {key : α → β} {entries : List α}
    (unique : (entries.map key).Nodup) {left right : α}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries)
    (same : key left = key right) : left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail ih =>
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (fresh (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (fresh (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih tailUnique leftTail rightTail

theorem Signature.ctor_eq_of_name_eq (signature : Signature)
    (accepted : signature.validate = .ok ())
    {datatype : DataDecl} (dataMember : datatype ∈ signature.datatypes)
    {left right : CtorDecl} (leftMember : left ∈ datatype.ctors)
    (rightMember : right ∈ datatype.ctors) (same : left.name = right.name) : left = right := by
  have global := signature.validate_ctorNamesUnique 256 accepted
  have localUnique : (datatype.ctors.map CtorDecl.name).Nodup :=
    (List.pairwise_flatMap.mp global).1 datatype dataMember
  exact eq_of_nodup_map localUnique leftMember rightMember same

theorem Signature.fields_formed (signature : Signature)
    (accepted : signature.validate = .ok ())
    {name : String} {datatype : DataDecl}
    (found : signature.findData name = some datatype)
    {constructor : CtorDecl} (constructorMember : constructor ∈ datatype.ctors)
    {arguments : List Ty} (arity : arguments.length = datatype.params)
    {context : Context} (argumentsScoped : ∀ argument ∈ arguments, argument.InScope context)
    {field : Ty} (fieldMember : field ∈ constructor.fields) :
    (Ty.instantiateParams arguments field).InScope context := by
  have declarationMember : datatype ∈ signature.datatypes := List.mem_of_find?_eq_some found
  have formed := Signature.modelReadyFrom_fields [] signature.datatypes
    (signature.validate_modelReady 256 accepted) datatype declarationMember
    constructor constructorMember field fieldMember
  exact Ty.instantiateParams_inScope arguments field context formed.1
    (arity.symm ▸ formed.2) argumentsScoped

end SystemFRK

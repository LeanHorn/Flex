import Flex.VCG.SystemFRK.Datatypes.Monotonicity

/-! Least-fixed-point interpretations of ordered positive datatypes. -/
namespace SystemFRK

namespace PredicateFix

def Below (left right : α → Prop) : Prop := ∀ x, left x → right x

def least (step : (α → Prop) → α → Prop) : α → Prop :=
  fun x => ∀ candidate, Below (step candidate) candidate → candidate x

theorem below (step : (α → Prop) → α → Prop) (candidate : α → Prop)
    (closed : Below (step candidate) candidate) : Below (least step) candidate :=
  fun _ h => h candidate closed

theorem equation (step : (α → Prop) → α → Prop)
    (mono : ∀ left right, Below left right → Below (step left) (step right)) :
    least step = step (least step) := by
  have fold : Below (step (least step)) (least step) := by
    intro x hx candidate closed
    exact closed x (mono _ _ (below step candidate closed) x hx)
  have unfold : Below (least step) (step (least step)) :=
    below step _ (mono _ _ fold)
  funext x
  exact propext ⟨unfold x, fold x⟩

end PredicateFix

theorem All₂.mono {first second : α → β → Prop}
    (included : ∀ a b, first a b → second a b)
    {as : List α} {bs : List β} (h : All₂ first as bs) : All₂ second as bs := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (included _ _ head) ih

theorem All₂.mono_mem {first second : α → β → Prop}
    {as : List α} {bs : List β} (h : All₂ first as bs)
    (included : ∀ a ∈ as, ∀ b, first a b → second a b) : All₂ second as bs := by
  induction h with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (included _ (by simp) _ head)
      (ih (fun a ha => included a (by simp [ha])))

def DataModel.override (model : DataModel) (name : String)
    (relation : List Candidate → Candidate) : DataModel :=
  ⟨fun other => if other = name then relation else model.datatype other⟩

/-- Constructor equation before substituting source-level type arguments. -/
def DataDecl.Interp (decl : DataDecl) (signature : Signature) (assignment : KAssignment)
    (model : DataModel) (args : List Candidate) (value : Value) : Prop :=
  args.length = decl.params ∧ ∃ ctor ∈ decl.ctors, ∃ fields,
    value = .ctor ctor.name fields ∧
      All₂ (fun fieldType field => fieldType.denote signature model assignment args [] field)
        ctor.fields fields

private def datatypeStep (signature : Signature) (assignment : KAssignment)
    (base : DataModel) (decl : DataDecl)
    (candidate : (List Candidate × Value) → Prop) : (List Candidate × Value) → Prop :=
  fun (args, value) => decl.Interp signature assignment
    (base.override decl.name (fun args value => candidate (args, value))) args value

private theorem datatypeStep_mono (signature : Signature) (assignment : KAssignment)
    (base : DataModel) (decl : DataDecl)
    (positive : ∀ ctor ∈ decl.ctors, ∀ field ∈ ctor.fields, field.positiveIn decl.name = true)
    (left right : (List Candidate × Value) → Prop) (included : PredicateFix.Below left right) :
    PredicateFix.Below (datatypeStep signature assignment base decl left)
      (datatypeStep signature assignment base decl right) := by
  rintro ⟨args, value⟩ ⟨arity, ctor, member, fields, shape, typed⟩
  refine ⟨arity, ctor, member, fields, shape, ?_⟩
  apply typed.mono_mem
  intro fieldType fieldMem field head
  exact Ty.denote_mono signature assignment decl.name _ _
    (by intro other different; simp [DataModel.override, different])
    (by simpa [DataModel.override] using fun args value => included (args, value))
    fieldType args [] (positive ctor member fieldType fieldMem) field head

/-- Add one datatype, taking its least positive interpretation over earlier ones. -/
def DataModel.add (signature : Signature) (assignment : KAssignment)
    (base : DataModel) (decl : DataDecl) : DataModel :=
  base.override decl.name (fun args value =>
    PredicateFix.least (datatypeStep signature assignment base decl) (args, value))

theorem DataModel.add_equation (signature : Signature) (assignment : KAssignment)
    (base : DataModel) (decl : DataDecl)
    (positive : ∀ ctor ∈ decl.ctors, ∀ field ∈ ctor.fields, field.positiveIn decl.name = true)
    (args : List Candidate) (value : Value) :
    (base.add signature assignment decl).datatype decl.name args value ↔
      decl.Interp signature assignment (base.add signature assignment decl) args value := by
  have equation := congrFun (PredicateFix.equation _
    (datatypeStep_mono signature assignment base decl positive)) (args, value)
  simpa only [DataModel.add, DataModel.override, if_pos rfl, ite_true, datatypeStep] using (iff_of_eq equation)

/-- All datatype equations characterized by the declarations processed so far. -/
def DataModel.Laws (signature : Signature) (assignment : KAssignment)
    (declarations : List DataDecl) (model : DataModel) : Prop :=
  ∀ name args value, model.datatype name args value ↔
    ∃ decl ∈ declarations, decl.name = name ∧ decl.Interp signature assignment model args value

/-- Earlier declarations mention only earlier datatype names. -/
def DataDecl.NamesClosed (names : List String) (decl : DataDecl) : Prop :=
  ∀ ctor ∈ decl.ctors, ∀ field ∈ ctor.fields, ∀ name ∈ field.dataNames, name ∈ names

def DeclarationsClosed (decls : List DataDecl) : Prop :=
  ∀ decl ∈ decls, decl.NamesClosed (decls.map (·.name))

theorem DataDecl.interp_model_congr (signature : Signature) (assignment : KAssignment)
    (decl : DataDecl) (left right : DataModel)
    (agree : ∀ ctor ∈ decl.ctors, ∀ field ∈ ctor.fields,
      ∀ name ∈ field.dataNames, left.datatype name = right.datatype name)
    (args : List Candidate) (value : Value) :
    decl.Interp signature assignment left args value ↔
      decl.Interp signature assignment right args value := by
  constructor
  · rintro ⟨arity, ctor, member, fields, shape, typed⟩
    refine ⟨arity, ctor, member, fields, shape, typed.mono_mem ?_⟩
    intro field hf v hv
    rwa [← field.model_congr signature assignment left right args [] (agree ctor member field hf)]
  · rintro ⟨arity, ctor, member, fields, shape, typed⟩
    refine ⟨arity, ctor, member, fields, shape, typed.mono_mem ?_⟩
    intro field hf v hv
    rwa [field.model_congr signature assignment left right args [] (agree ctor member field hf)]

theorem DataModel.add_laws (signature : Signature) (assignment : KAssignment)
    (decls : List DataDecl) (base : DataModel) (decl : DataDecl)
    (closed : DeclarationsClosed decls) (ready : decl.Ready (decls.map (·.name)))
    (laws : base.Laws signature assignment decls) :
    (base.add signature assignment decl).Laws signature assignment (decl :: decls) := by
  have previous (old : DataDecl) (member : old ∈ decls) (args : List Candidate) (value : Value) :
      old.Interp signature assignment base args value ↔
        old.Interp signature assignment (base.add signature assignment decl) args value := by
    apply old.interp_model_congr signature assignment base (base.add signature assignment decl)
    intro ctor hc field hf name hn
    have notCurrent : name ≠ decl.name := by
      intro eq
      exact ready.1 (eq ▸ closed old member ctor hc field hf name hn)
    simp [DataModel.add, DataModel.override, notCurrent]
  intro name args value
  by_cases same : name = decl.name
  · subst name
    rw [base.add_equation signature assignment decl (fun c hc f hf => (ready.2 c hc f hf).2.2.1)]
    constructor
    · intro h; exact ⟨decl, by simp, rfl, h⟩
    · rintro ⟨old, member, nameEq, h⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact h
      · exact False.elim (ready.1 (nameEq ▸ List.mem_map.mpr ⟨old, member, rfl⟩))
  · have unchanged : (base.add signature assignment decl).datatype name = base.datatype name := by
      simp [DataModel.add, DataModel.override, same]
    rw [unchanged, laws name args value]
    constructor
    · rintro ⟨old, member, nameEq, h⟩
      exact ⟨old, by simp [member], nameEq, (previous old member args value).mp h⟩
    · rintro ⟨old, member, nameEq, h⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact False.elim (same nameEq.symm)
      · exact ⟨old, member, nameEq, (previous old member args value).mpr h⟩

private theorem declarationsClosed_cons (decls : List DataDecl) (decl : DataDecl)
    (closed : DeclarationsClosed decls) (ready : decl.Ready (decls.map (·.name))) :
    DeclarationsClosed (decl :: decls) := by
  intro old member ctor hc field hf name hn
  rcases List.mem_cons.mp member with rfl | member
  · exact (ready.2 ctor hc field hf).2.2.2 name hn
  · exact List.mem_cons_of_mem _ (closed old member ctor hc field hf name hn)

/-- Interpret declarations in order, retaining all previously established laws. -/
def DataModel.build (signature : Signature) (assignment : KAssignment)
    (base : DataModel) : List DataDecl → DataModel
  | [] => base
  | decl :: rest => build signature assignment (base.add signature assignment decl) rest

theorem DataModel.build_laws (signature : Signature) (assignment : KAssignment)
    (remaining : List DataDecl) (processed : List DataDecl) (base : DataModel)
    (closed : DeclarationsClosed processed)
    (ready : Signature.modelReadyFrom (processed.map (·.name)) remaining = true)
    (laws : base.Laws signature assignment processed) :
    (base.build signature assignment remaining).Laws signature assignment (processed ++ remaining) := by
  induction remaining generalizing processed base with
  | nil => simpa only [DataModel.build, List.append_nil] using laws
  | cons decl rest ih =>
    simp only [Signature.modelReadyFrom, Bool.and_eq_true] at ready
    have headReady := (decl.ready_iff (processed.map (·.name))).mp ready.1
    have previous := ih (decl :: processed) (base.add signature assignment decl)
      (declarationsClosed_cons processed decl closed headReady) ready.2
      (base.add_laws signature assignment processed decl closed headReady laws)
    simpa only [DataModel.build, DataModel.Laws, List.mem_append, List.mem_cons,
      or_assoc, or_left_comm] using previous

def Signature.datatypeModel (signature : Signature) (assignment : KAssignment) : DataModel :=
  DataModel.build signature assignment ⟨fun _ _ _ => False⟩ signature.datatypes

theorem Signature.datatypeModel_laws (signature : Signature) (assignment : KAssignment)
    (ready : signature.modelReady = true) :
    (signature.datatypeModel assignment).Laws signature assignment signature.datatypes := by
  have result := DataModel.build_laws signature assignment signature.datatypes []
    ⟨fun _ _ _ => False⟩ (by simp [DeclarationsClosed]) ready
    (by simp [DataModel.Laws])
  simpa only [List.nil_append, Signature.datatypeModel] using result

end SystemFRK

import Flex.VCG.LambdaRK.BindingLemmas

/-! Structural formation evidence used to construct datatype interpretations.
The executable signature checker retains its detailed diagnostics; these checks
record the semantic conditions independently of its fuel and error messages. -/
namespace LambdaRK

/-- Datatype names occurring anywhere in a type, including its arguments. -/
def Ty.dataNames : Ty → List String
  | .var _ | .int | .bool => []
  | .data name args => name :: args.flatMap Ty.dataNames
  | .arrow _ a b => a.dataNames ++ b.dataNames
  | .all a | .refine a _ => a.dataNames

/-- Declaration fields contain no refinements. Parameters may later be
instantiated with refined types. -/
def Ty.isRaw : Ty → Bool
  | .var _ | .int | .bool => true
  | .data _ args => (args.map Ty.isRaw).all id
  | .arrow _ a b => a.isRaw && b.isRaw
  | .all a => a.isRaw
  | .refine _ _ => false

/-- Positivity in one datatype interpretation. Its occurrences are excluded
from domains and from arguments to other datatype interpretations. -/
def Ty.positiveIn (name : String) : Ty → Bool
  | .var _ | .int | .bool => true
  | .data _ args => args.all (fun a => !a.dataNames.contains name)
  | .arrow _ a b => !a.dataNames.contains name && b.positiveIn name
  | .all a => a.positiveIn name
  | .refine _ _ => false

def Ty.indicesScoped (depth : Nat) : Ty → Bool
  | .var i => i < depth
  | .int | .bool => true
  | .data _ args => (args.map (Ty.indicesScoped depth)).all id
  | .arrow _ a b => a.indicesScoped depth && b.indicesScoped depth
  | .all a => a.indicesScoped (depth + 1)
  | .refine a _ => a.indicesScoped depth

theorem Ty.indicesScoped_eq_true (ty : Ty) (depth : Nat) :
    ty.indicesScoped depth = true ↔ ty.TypeScoped depth := by
  induction ty using Ty.rec
    (motive_2 := fun ts => ∀ depth,
      ts.all (Ty.indicesScoped depth) = true ↔ ∀ t ∈ ts, t.TypeScoped depth)
    generalizing depth with
  | _ => simp_all [Ty.indicesScoped, Ty.TypeScoped]

/-- Conditions needed for a single declaration over earlier datatype names. -/
def DataDecl.modelReady (earlier : List String) (decl : DataDecl) : Bool :=
  !earlier.contains decl.name && decl.ctors.all (fun ctor => ctor.fields.all fun field =>
    field.isRaw && field.indicesScoped decl.params && field.positiveIn decl.name &&
      field.dataNames.all (fun name => (decl.name :: earlier).contains name))

def Signature.modelReadyFrom (earlier : List String) : List DataDecl → Bool
  | [] => true
  | decl :: rest => decl.modelReady earlier && modelReadyFrom (decl.name :: earlier) rest

def Signature.modelReady (sig : Signature) : Bool := Signature.modelReadyFrom [] sig.datatypes

def DataDecl.Ready (earlier : List String) (decl : DataDecl) : Prop :=
  decl.name ∉ earlier ∧ ∀ ctor ∈ decl.ctors, ∀ field ∈ ctor.fields,
    field.isRaw = true ∧ field.TypeScoped decl.params ∧ field.positiveIn decl.name = true ∧
      ∀ name ∈ field.dataNames, name ∈ decl.name :: earlier

theorem DataDecl.ready_iff (earlier : List String) (decl : DataDecl) :
    decl.modelReady earlier = true ↔ decl.Ready earlier := by
  simp [DataDecl.modelReady, DataDecl.Ready, Ty.indicesScoped_eq_true, and_assoc]

theorem Signature.modelReadyFrom_names (earlier : List String) (decls : List DataDecl)
    (ready : modelReadyFrom earlier decls = true) :
    (decls.map (·.name)).Nodup ∧ ∀ decl ∈ decls, decl.name ∉ earlier := by
  induction decls generalizing earlier with
  | nil => simp
  | cons decl rest ih =>
    simp only [modelReadyFrom, Bool.and_eq_true] at ready
    have head := (decl.ready_iff earlier).mp ready.1
    obtain ⟨tailUnique, tailFresh⟩ := ih (decl.name :: earlier) ready.2
    constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_, tailUnique⟩
      intro member
      obtain ⟨old, oldMem, same⟩ := List.mem_map.mp member
      exact tailFresh old oldMem (by simp [same])
    · intro old member
      rcases List.mem_cons.mp member with rfl | member
      · exact head.1
      · intro bad
        exact tailFresh old member (by simp [bad])

theorem Signature.modelReadyFrom_fields (earlier : List String) (decls : List DataDecl)
    (ready : modelReadyFrom earlier decls = true) :
    ∀ decl ∈ decls, ∀ ctor ∈ decl.ctors, ∀ field ∈ ctor.fields,
      field.isRaw = true ∧ field.TypeScoped decl.params := by
  induction decls generalizing earlier with
  | nil => simp
  | cons decl rest ih =>
    simp only [modelReadyFrom, Bool.and_eq_true] at ready
    intro old member ctor hc field hf
    rcases List.mem_cons.mp member with rfl | member
    · have fieldReady := ((old.ready_iff earlier).mp ready.1).2 ctor hc field hf
      exact ⟨fieldReady.1, fieldReady.2.1⟩
    · exact ih (decl.name :: earlier) ready.2 old member ctor hc field hf

end LambdaRK

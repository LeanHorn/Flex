import Flex.VCG.LambdaRK.Context
import Flex.VCG.LambdaRK.TypeIndexLemmas
import Flex.VCG.LambdaRK.AlphaLemmas

/-! Scope of datatype-field instantiation. Raw declarations acquire logical
variables only from their type arguments, including underneath polymorphic
and function fields. -/
namespace LambdaRK

theorem Ty.freshenBindersAux_isRaw (type : Ty) (avoid : List String)
    (renames : List (String × String)) :
    (type.freshenBindersAux avoid renames).isRaw = type.isRaw := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ avoid renames,
      ((ts.map (·.freshenBindersAux avoid renames)).map Ty.isRaw).all id =
        (ts.map Ty.isRaw).all id) generalizing avoid renames with
  | _ => simp_all [Ty.freshenBindersAux, Ty.isRaw]

theorem Ty.freshenBinders_isRaw (type : Ty) (avoid : List String) :
    (type.freshenBinders avoid).isRaw = type.isRaw :=
  type.freshenBindersAux_isRaw _ []

/-- Inserting types into a raw field introduces no other logical free names. -/
theorem Ty.mapTypes_raw_freeVars (type : Ty) (f : Nat → Nat → Ty)
    (permitted : String → Prop) (depth : Nat) (raw : type.isRaw = true)
    (replacementNames : ∀ d i name, name ∈ (f d i).freeVars → permitted name) :
    ∀ name ∈ (type.mapTypes f depth).freeVars, permitted name := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ depth, (ts.map Ty.isRaw).all id = true →
      ∀ name ∈ (ts.map (·.mapTypes f depth)).flatMap Ty.freeVars, permitted name)
    generalizing depth with
  | var index => simpa [Ty.mapTypes] using replacementNames depth index
  | int => simp [Ty.mapTypes, Ty.freeVars]
  | bool => simp [Ty.mapTypes, Ty.freeVars]
  | data name arguments ih =>
    simpa only [Ty.mapTypes, Ty.freeVars] using ih depth (by simpa [Ty.isRaw] using raw)
  | arrow binder domain codomain domainIH codomainIH =>
    simp only [Ty.isRaw, Bool.and_eq_true] at raw
    intro name member
    simp only [Ty.mapTypes, Ty.freeVars, List.mem_append, List.mem_filter, bne_iff_ne] at member
    rcases member with member | ⟨member, _⟩
    · exact domainIH depth raw.1 name member
    · exact codomainIH depth raw.2 name member
  | all body ih =>
    simpa only [Ty.mapTypes, Ty.freeVars] using ih (depth + 1) (by simpa [Ty.isRaw] using raw)
  | refine base predicate ih => simp [Ty.isRaw] at raw
  | nil => rename_i depth raw name member; simp at member
  | cons head tail headIH tailIH =>
    rename_i depth raw name member
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at raw
    simp only [List.map_cons, List.flatMap_cons, List.mem_append] at member
    rcases member with member | member
    · exact headIH depth raw.1 name member
    · exact tailIH depth raw.2 name member

/-- Instantiating a well-scoped raw constructor field with in-scope arguments
produces an in-scope program type. -/
theorem Ty.instantiateParams_inScope (arguments : List Ty) (field : Ty)
    (context : Context) (raw : field.isRaw = true)
    (fieldScoped : field.TypeScoped arguments.length)
    (argumentsScoped : ∀ argument ∈ arguments, argument.InScope context) :
    (Ty.instantiateParams arguments field).InScope context := by
  constructor
  · exact Ty.instantiateParams_scoped arguments field context.typeDepth fieldScoped
      (fun argument member => (argumentsScoped argument member).1)
  · unfold Ty.instantiateParams
    apply Ty.mapTypes_raw_freeVars _ _ (fun name => name ∈ context.names) 0
    · rwa [Ty.freshenBinders_isRaw]
    · intro depth index name member
      split at member
      · simp [Ty.freeVars] at member
      · split at member
        · rename_i replacement found
          rw [Ty.shiftTypes_freeVars] at member
          obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? found)
          exact (argumentsScoped argument argumentMember).2 name
            ((argument.freshenBinders_freeVars _ name).mp member)
        · simp [Ty.freeVars] at member

theorem Ty.outerBase_inScope {type : Ty} {context : Context}
    (hasScope : type.InScope context) : type.outerBase.InScope context := by
  induction type using Ty.rec
    (motive_2 := fun _ => True) with
  | refine base predicate ih =>
    apply ih
    constructor
    · simpa [Ty.TypeScoped] using hasScope.1
    · intro name member
      exact hasScope.2 name (by simp [Ty.freeVars, member])
  | nil | cons => trivial
  | _ => exact hasScope

theorem Ty.data_arguments_inScope {name : String} {arguments : List Ty} {context : Context}
    (hasScope : (Ty.data name arguments).InScope context)
    {argument : Ty} (member : argument ∈ arguments) : argument.InScope context := by
  constructor
  · exact (show ∀ a ∈ arguments, a.TypeScoped context.typeDepth by
      simpa [Ty.TypeScoped] using hasScope.1) argument member
  · intro name free
    exact hasScope.2 name (by simpa [Ty.freeVars] using
      (List.mem_flatMap.mpr ⟨argument, member, free⟩ : name ∈ arguments.flatMap Ty.freeVars))

end LambdaRK

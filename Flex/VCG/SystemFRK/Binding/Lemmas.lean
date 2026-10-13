import Flex.VCG.SystemFRK.Binding

/-! Syntactic binding laws. -/

namespace SystemFRK

theorem Ty.freshenBindersAux_scoped (ty : Ty) (depth : Nat)
    (avoid : List String) (renames : List (String × String)) :
    (ty.freshenBindersAux avoid renames).TypeScoped depth ↔ ty.TypeScoped depth := by
  induction ty using Ty.rec
    (motive_2 := fun ts => ∀ depth avoid renames,
      (∀ t ∈ ts.map (·.freshenBindersAux avoid renames), t.TypeScoped depth) ↔
        ∀ t ∈ ts, t.TypeScoped depth) generalizing depth avoid renames with
  | var => simp [Ty.freshenBindersAux, Ty.TypeScoped]
  | int => simp [Ty.freshenBindersAux, Ty.TypeScoped]
  | bool => simp [Ty.freshenBindersAux, Ty.TypeScoped]
  | data => simp_all [Ty.freshenBindersAux, Ty.TypeScoped]
  | arrow => simp_all [Ty.freshenBindersAux, Ty.TypeScoped]
  | all => simp_all [Ty.freshenBindersAux, Ty.TypeScoped]
  | refine => simp_all [Ty.freshenBindersAux, Ty.TypeScoped]
  | nil => simp
  | cons => simp_all

theorem Ty.freshenBinders_scoped (ty : Ty) (depth : Nat) (avoid : List String) :
    (ty.freshenBinders avoid).TypeScoped depth ↔ ty.TypeScoped depth :=
  ty.freshenBindersAux_scoped depth _ []

@[simp] theorem LTerm.substTerm_self (term : LTerm) (name : String) :
    term.substTerm name (.var name) = term := by
  induction term using LTerm.rec
    (motive_2 := fun terms => terms.map (·.substTerm name (.var name)) = terms) with
  | var x => simp [LTerm.substTerm]; exact Eq.symm
  | _ => simp_all [LTerm.substTerm]

@[simp] theorem Formula.substTerm_self (formula : Formula) (name : String) :
    formula.substTerm name (.var name) = formula := by
  induction formula <;> simp_all [Formula.substTerm]

@[simp] theorem Atom.substTerm_self (atom : Atom) (name : String) :
    atom.substTerm name (.var name) = atom := by
  cases atom <;> simp [Atom.substTerm]

theorem LTerm.substTerm_of_not_mem (term : LTerm) (name : String)
    (replacement : LTerm) (fresh : name ∉ term.freeVars) :
    term.substTerm name replacement = term := by
  induction term using LTerm.rec
    (motive_2 := fun terms => name ∉ terms.flatMap LTerm.freeVars →
      terms.map (·.substTerm name replacement) = terms) with
  | var x =>
    have distinct : x ≠ name := fun equal => fresh (by simp [LTerm.freeVars, equal])
    simp [LTerm.substTerm, distinct]
  | _ => simp_all [LTerm.freeVars, LTerm.substTerm]

theorem Formula.substTerm_of_not_mem (formula : Formula) (name : String)
    (replacement : LTerm) (fresh : name ∉ formula.freeVars) :
    formula.substTerm name replacement = formula := by
  induction formula <;>
    simp_all [Formula.freeVars, Formula.substTerm, LTerm.substTerm_of_not_mem]

theorem Atom.substTerm_of_not_mem (atom : Atom) (name : String)
    (replacement : LTerm) (fresh : name ∉ atom.freeVars) :
    atom.substTerm name replacement = atom := by
  cases atom with
  | theory formula =>
    simp_all [Atom.freeVars, Atom.substTerm, Formula.substTerm_of_not_mem]
  | kvar k args =>
    simp only [Atom.freeVars, List.mem_flatMap, not_exists, not_and] at fresh
    simp only [Atom.substTerm, Atom.kvar.injEq, true_and]
    simpa using List.map_congr_left (l := args)
      (f := fun term => term.substTerm name replacement) (g := id)
      (fun term mem => LTerm.substTerm_of_not_mem term name replacement (fresh term mem))

@[simp] theorem Ty.mapTypes_id (ty : Ty) (depth : Nat) :
    ty.mapTypes (fun _ i => .var i) depth = ty := by
  induction ty using Ty.rec
    (motive_2 := fun types => ∀ depth,
      types.map (·.mapTypes (fun _ i => .var i) depth) = types) generalizing depth with
  | _ => simp_all [Ty.mapTypes]

@[simp] theorem Ty.shiftTypes_zero (ty : Ty) (cutoff : Nat) :
    ty.shiftTypes 0 cutoff = ty := by
  simp [Ty.shiftTypes]

theorem Ty.mapTypes_freeVars (ty : Ty) (indices : Nat → Nat → Nat) (depth : Nat) :
    (ty.mapTypes (fun d i => .var (indices d i)) depth).freeVars = ty.freeVars := by
  induction ty using Ty.rec
    (motive_2 := fun types => ∀ depth,
      (types.map (·.mapTypes (fun d i => .var (indices d i)) depth)).flatMap Ty.freeVars =
        types.flatMap Ty.freeVars) generalizing depth with
  | _ => simp_all [Ty.mapTypes, Ty.freeVars]

@[simp] theorem Ty.shiftTypes_freeVars (ty : Ty) (amount cutoff : Nat) :
    (ty.shiftTypes amount cutoff).freeVars = ty.freeVars := by
  exact ty.mapTypes_freeVars _ 0

@[simp] theorem Ty.stripRefinements_idempotent (ty : Ty) :
    ty.stripRefinements.stripRefinements = ty.stripRefinements := by
  induction ty using Ty.rec
    (motive_2 := fun types =>
      (types.map Ty.stripRefinements).map Ty.stripRefinements =
        types.map Ty.stripRefinements) with
  | _ => simp_all [Ty.stripRefinements]

end SystemFRK

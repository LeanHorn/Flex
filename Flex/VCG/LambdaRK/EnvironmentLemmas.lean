import Flex.VCG.LambdaRK.LogicalLemmas

/-! Environment agreement for logical predicates and semantic types.
These proofs do not depend on any draft theorem. -/
namespace LambdaRK

theorem LogicalListEval.environment_congr
    (signature : Signature) (left right : Environment) (terms : List LTerm)
    (values : List Value)
    (agree : ∀ name ∈ terms.flatMap LTerm.freeVars, left.lookup name = right.lookup name) :
    LogicalListEval signature left terms values ↔ LogicalListEval signature right terms values := by
  induction terms generalizing values with
  | nil => constructor <;> intro h <;> cases h <;> constructor
  | cons term terms ih =>
    have head := LogicalEval.environment_congr signature left right term
    have tail := ih
    constructor
    · intro h
      cases h with
      | cons h t =>
        exact .cons ((head _ (fun n hn => agree n (by simp [hn]))).mp h)
          ((tail _ (fun n hn => agree n (by simp [hn]))).mp t)
    · intro h
      cases h with
      | cons h t =>
        exact .cons ((head _ (fun n hn => agree n (by simp [hn]))).mpr h)
          ((tail _ (fun n hn => agree n (by simp [hn]))).mpr t)

theorem Formula.environment_congr
    (signature : Signature) (left right : Environment) (formula : Formula)
    (agree : ∀ name ∈ formula.freeVars, left.lookup name = right.lookup name) :
    formula.denote signature left ↔ formula.denote signature right := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | eq a b | le a b =>
    have ha := LogicalEval.environment_congr signature left right a
      (agree := fun n hn => agree n (by simp [Formula.freeVars, hn]))
    have hb := LogicalEval.environment_congr signature left right b
      (agree := fun n hn => agree n (by simp [Formula.freeVars, hn]))
    simp only [Formula.denote, ha, hb]
  | and a b ia ib =>
    exact and_congr (ia (fun n hn => agree n (by simp [Formula.freeVars, hn])))
      (ib (fun n hn => agree n (by simp [Formula.freeVars, hn])))
  | or a b ia ib =>
    exact or_congr (ia (fun n hn => agree n (by simp [Formula.freeVars, hn])))
      (ib (fun n hn => agree n (by simp [Formula.freeVars, hn])))
  | not a ih => exact not_congr (ih agree)

theorem Atom.environment_congr
    (signature : Signature) (assignment : KAssignment) (left right : Environment) (atom : Atom)
    (agree : ∀ name ∈ atom.freeVars, left.lookup name = right.lookup name) :
    atom.denote signature assignment left ↔ atom.denote signature assignment right := by
  cases atom with
  | theory formula => exact formula.environment_congr signature left right agree
  | kvar name terms =>
    simp only [Atom.denote, LogicalListEval.environment_congr signature left right terms _ agree]

theorem Ty.environment_congr
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (type : Ty) (types : TypeEnvironment) (left right : Environment)
    (agree : ∀ name ∈ type.freeVars, left.lookup name = right.lookup name) :
    type.denote signature model assignment types left =
      type.denote signature model assignment types right := by
  induction type using Ty.rec
      (motive_2 := fun ts => ∀ types left right,
        (∀ name ∈ ts.flatMap Ty.freeVars, left.lookup name = right.lookup name) →
        ts.map (Ty.denote signature model assignment types left) =
          ts.map (Ty.denote signature model assignment types right))
      generalizing types left right with
  | var => simp only [Ty.denote]
  | int => simp only [Ty.denote]
  | bool => simp only [Ty.denote]
  | data name args ih =>
    simp only [Ty.denote]
    exact congrArg (model.datatype name) (ih types left right (by simpa [Ty.freeVars] using agree))
  | arrow name domain codomain ihD ihC =>
    have dom := ihD types left right (fun n hn => agree n (by simp [Ty.freeVars, hn]))
    have cod (v : Value) := ihC types (left.bind name v) (right.bind name v) (by
      intro n hn
      by_cases h : n = name
      · subst n; simp [Environment.bind]
      · simpa [Environment.bind, List.lookup_cons, show (n == name) = false from by simpa using h] using
          agree n (by simp [Ty.freeVars, hn, h]))
    simp only [Ty.denote, dom, cod]
  | all body ih =>
    simp only [Ty.denote, ih _ left right (by simpa [Ty.freeVars] using agree)]
  | refine base atom ih =>
    have hb := ih types left right (fun n hn => agree n (by simp [Ty.freeVars, hn]))
    have hp (v : Value) := atom.environment_congr signature assignment
      (left.bind valueName v) (right.bind valueName v) (by
        intro n hn
        by_cases h : n = valueName
        · subst n; simp [Environment.bind]
        · simpa [Environment.bind, List.lookup_cons, show (n == valueName) = false from by simpa using h] using
            agree n (by simp [Ty.freeVars, hn, h]))
    funext v
    simp only [Ty.denote, hb]
    exact propext (and_congr Iff.rfl (hp v))
  | nil => rfl
  | cons t ts ih it =>
    rename_i types left right agree
    simp only [List.map_cons]
    rw [ih types left right (fun n hn => agree n (by simp [hn])),
      it types left right (fun n hn => agree n (by simp [hn]))]

end LambdaRK

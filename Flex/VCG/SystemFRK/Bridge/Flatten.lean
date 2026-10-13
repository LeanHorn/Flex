import Flex.VCG.SystemFRK.Bridge.Lower
import Flex.VCG.SystemFRK.Model

/-! Source-clause certificates reconstruct the original constraint. -/
namespace SystemFRK.Bridge

@[simp] theorem wrapFrames_append (left right : List SourceFrame) (body : Cstr) :
    wrapFrames (left ++ right) body = wrapFrames left (wrapFrames right body) := by
  simp [wrapFrames, List.foldr_append]

@[simp] theorem wrapFrames_cons (frame : SourceFrame) (frames : List SourceFrame)
    (body : Cstr) :
    wrapFrames (frame :: frames) body = frame.wrap (wrapFrames frames body) := rfl

private theorem wrapFrames_conj (frames : List SourceFrame) (left right : Cstr)
    (signature : Signature) (assignment : KAssignment) (environment : Environment) :
    (wrapFrames frames (.conj left right)).denote signature assignment environment ↔
      (wrapFrames frames left).denote signature assignment environment ∧
      (wrapFrames frames right).denote signature assignment environment := by
  induction frames generalizing environment with
  | nil => rfl
  | cons frame frames ih =>
      cases frame <;>
        simp only [wrapFrames_cons, SourceFrame.wrap, Cstr.denote, ih, forall_and]

private theorem wrapFrames_truth (frames : List SourceFrame)
    (signature : Signature) (assignment : KAssignment) :
    (wrapFrames frames .truth).Valid signature assignment := by
  intro environment
  induction frames generalizing environment with
  | nil => trivial
  | cons frame frames ih =>
      cases frame with
      | all name sort =>
          intro value _
          exact ih (environment.bind name value)
      | guard atom => intro _; exact ih environment

private theorem flattenAux_sound (constraint : Cstr) (frames : List SourceFrame)
    (path : List Nat) (next : Nat) (signature : Signature) (assignment : KAssignment)
    (certified : ∀ source ∈ (flattenAux constraint frames path next).1,
      source.constraint.Valid signature assignment) :
    (wrapFrames frames constraint).Valid signature assignment := by
  induction constraint generalizing frames path next with
  | truth => exact wrapFrames_truth frames signature assignment
  | head atom =>
      exact certified ⟨next, path, frames, atom⟩ (by simp [flattenAux])
  | all name sort body ih =>
      have bodyProof := ih (frames ++ [SourceFrame.all name sort]) (path ++ [2]) next
        (by simpa only [flattenAux] using certified)
      rw [wrapFrames_append] at bodyProof
      exact bodyProof
  | guard atom body ih =>
      have bodyProof := ih (frames ++ [SourceFrame.guard atom]) (path ++ [2]) next
        (by simpa only [flattenAux] using certified)
      rw [wrapFrames_append] at bodyProof
      exact bodyProof
  | conj left right leftIH rightIH =>
      have leftProof := leftIH frames (path ++ [0]) next (by
        intro source member
        apply certified source
        simp only [flattenAux, List.mem_append]
        exact Or.inl member)
      have rightProof := rightIH frames (path ++ [1])
        (flattenAux left frames (path ++ [0]) next).2 (by
          intro source member
          apply certified source
          simp only [flattenAux, List.mem_append]
          exact Or.inr member)
      intro environment
      exact (wrapFrames_conj frames left right signature assignment environment).mpr
        ⟨leftProof environment, rightProof environment⟩

/-- Checked source-clause certificates suffice for the original, unflattened
constraint. This theorem has no dependency on scalarization or solver output. -/
theorem flatten_sound (signature : Signature) (assignment : KAssignment)
    (constraint : Cstr)
    (certified : ∀ source ∈ flatten constraint,
      source.constraint.Valid signature assignment) :
    constraint.Valid signature assignment := by
  apply flattenAux_sound constraint [] [] 0 signature assignment
  intro source member
  apply certified source
  simpa only [flatten, List.mem_toArray] using member

/-- A conjunction-shaped certificate interface for the proof-producing adapter. -/
def ClausesValid (signature : Signature) (assignment : KAssignment) : List Cstr → Prop
  | [] => True
  | constraint :: constraints =>
      constraint.Valid signature assignment ∧ ClausesValid signature assignment constraints

private theorem ClausesValid.member (signature : Signature) (assignment : KAssignment)
    (constraints : List Cstr) (certified : ClausesValid signature assignment constraints)
    (constraint : Cstr) (member : constraint ∈ constraints) :
    constraint.Valid signature assignment := by
  induction constraints with
  | nil => cases member
  | cons head tail ih =>
      cases List.mem_cons.mp member with
      | inl equality => subst constraint; exact certified.1
      | inr member => exact ih certified.2 member

theorem flatten_valid_sound (signature : Signature) (assignment : KAssignment)
    (constraint : Cstr)
    (certified : ClausesValid signature assignment
      ((flatten constraint).toList.map SourceClause.constraint)) :
    constraint.Valid signature assignment := by
  apply flatten_sound signature assignment constraint
  intro source member
  apply ClausesValid.member signature assignment _ certified source.constraint
  exact List.mem_map.mpr ⟨source, Array.mem_toList_iff.mpr member, rfl⟩

end SystemFRK.Bridge

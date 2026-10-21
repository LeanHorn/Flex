import Init

set_option maxRecDepth 4096

namespace «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive6-2_000»

-- Statements

section
set_option Elab.async false

-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive6-2_000.smt2":62:1-62:12 (check-sat, command 10)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive6-2_000.smt2":8:1-17:2 (clause 1, command 5)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive6-2_000.smt2":18:1-28:2 (clause 2, command 6)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive6-2_000.smt2":29:1-39:2 (clause 3, command 7)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive6-2_000.smt2":40:1-49:2 (clause 4, command 8)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive6-2_000.smt2":50:1-60:2 (clause 5, command 9)
/-- There are interpretations of the declared symbols satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Int → Int → Prop),
  ∃ (r1 : Int → Int → Prop),
  ∃ (r2 : Int → Int → Prop),
  (∀ (A B : Int),
  (A = (-1 : Int) + B) →
  r1 A B) ∧
  ((∀ (A B C D : Int),
  (r1 A D) →
  (¬(0 : Int) = C) →
  (¬((0 : Int) = C) = (B ≥ (3 : Int))) →
  r0 A D) ∧
  ((∀ (A B C D : Int),
  (r0 D B) →
  (¬(0 : Int) = C) →
  (A = D) →
  (((0 : Int) = C) = (B ≤ (0 : Int))) →
  r2 A B) ∧
  ((∀ (A B C : Int),
  ((0 : Int) = C) →
  (A = (1 : Int)) →
  (((0 : Int) = C) = (B ≤ (0 : Int))) →
  r2 A B) ∧
  (∀ (A B C D : Int),
  (r2 C A) →
  (((0 : Int) = D) = (C ≤ (0 : Int))) →
  (¬(0 : Int) = B) →
  ((0 : Int) = D) →
  (¬((0 : Int) = B) = (A ≥ (3 : Int))) →
  False))))

end

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of a satisfying interpretation.
theorem problem : Problem := by
  sorry

end «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive6-2_000»

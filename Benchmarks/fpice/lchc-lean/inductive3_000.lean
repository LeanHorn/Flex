import Init

set_option maxRecDepth 4096

namespace «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive3_000»

-- Statements

section
set_option Elab.async false

-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive3_000.smt2":58:1-58:12 (check-sat, command 7)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive3_000.smt2":6:1-16:2 (clause 1, command 3)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive3_000.smt2":17:1-31:2 (clause 2, command 4)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive3_000.smt2":32:1-45:2 (clause 3, command 5)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive3_000.smt2":46:1-56:2 (clause 4, command 6)
/-- There are interpretations of the declared symbols satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Int → Int → Prop),
  (∀ (A B C D E : Int),
  (r0 E D) →
  (¬(0 : Int) = C) →
  (D = (-2 : Int)) →
  (A = E) →
  (((0 : Int) = C) = ((-1 : Int) ≤ B)) →
  r0 A B) ∧
  ((∀ (A B C D E : Int),
  (((0 : Int) = C) = ((-1 : Int) ≤ B)) →
  (¬(0 : Int) = D) →
  ((0 : Int) = C) →
  (A = (-1 : Int) + E) →
  (E = (2 : Int) * B) →
  (¬((0 : Int) = D) = (B ≤ (1 : Int))) →
  r0 A B) ∧
  ((∀ (A B C D : Int),
  (¬((0 : Int) = D) = (B ≤ (1 : Int))) →
  ((0 : Int) = C) →
  ((0 : Int) = D) →
  (A = B) →
  (((0 : Int) = C) = ((-1 : Int) ≤ B)) →
  r0 A B) ∧
  (∀ (A B C : Int),
  (r0 B A) →
  ((0 : Int) = C) →
  (A = (3 : Int)) →
  (¬((0 : Int) = C) = (B ≥ (0 : Int))) →
  False)))

end

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of a satisfying interpretation.
theorem problem : Problem := by
  sorry

end «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive3_000»

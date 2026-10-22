import Init

set_option maxRecDepth 4096

namespace «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive5_000»

-- Statements

section
set_option Elab.async false

-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive5_000.smt2":79:1-79:12 (check-sat, command 8)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive5_000.smt2":6:1-24:2 (clause 1, command 3)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive5_000.smt2":25:1-35:2 (clause 2, command 4)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive5_000.smt2":36:1-50:2 (clause 3, command 5)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive5_000.smt2":51:1-66:2 (clause 4, command 6)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive5_000.smt2":67:1-77:2 (clause 5, command 7)
/-- There are interpretations of the declared symbols satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Int → Int → Prop),
  (∀ (A B C D E F G H : Int),
  (r0 H G) →
  (((0 : Int) = D) = ((2 : Int) ≤ B)) →
  (((0 : Int) = C) = ((-2 : Int) ≤ B)) →
  (¬(0 : Int) = E) →
  ((0 : Int) = D) →
  ((0 : Int) = C) →
  (G = (-1 : Int) + F) →
  (F = (2 : Int) * B) →
  (A = H) →
  (¬((0 : Int) = E) = (B ≤ (2 : Int))) →
  r0 A B) ∧
  ((∀ (A B C D E : Int),
  (r0 E D) →
  (¬(0 : Int) = C) →
  (D = (-3 : Int)) →
  (A = E) →
  (((0 : Int) = C) = ((-2 : Int) ≤ B)) →
  r0 A B) ∧
  ((∀ (A B C D E : Int),
  (((0 : Int) = C) = ((-2 : Int) ≤ B)) →
  (¬(0 : Int) = D) →
  ((0 : Int) = C) →
  (A = (-1 : Int) + E) →
  (E = (2 : Int) * B) →
  (((0 : Int) = D) = ((2 : Int) ≤ B)) →
  r0 A B) ∧
  ((∀ (A B C D E : Int),
  (((0 : Int) = C) = ((-2 : Int) ≤ B)) →
  (¬((0 : Int) = E) = (B ≤ (2 : Int))) →
  ((0 : Int) = D) →
  ((0 : Int) = C) →
  ((0 : Int) = E) →
  (A = B) →
  (((0 : Int) = D) = ((2 : Int) ≤ B)) →
  r0 A B) ∧
  (∀ (A B C : Int),
  (r0 B A) →
  ((0 : Int) = C) →
  (A = (3 : Int)) →
  (¬((0 : Int) = C) = (B ≥ (0 : Int))) →
  False))))

end

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of a satisfying interpretation.
theorem problem : Problem := by
  sorry

end «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive5_000»

import Init

set_option maxRecDepth 4096

namespace «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive_000»

-- Statements

section
set_option Elab.async false

-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":111:1-111:12 (check-sat, command 11)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":7:1-24:2 (clause 1, command 4)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":25:1-41:2 (clause 2, command 5)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":42:1-60:2 (clause 3, command 6)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":61:1-70:2 (clause 4, command 7)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":71:1-88:2 (clause 5, command 8)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":89:1-99:2 (clause 6, command 9)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive_000.smt2":100:1-109:2 (clause 7, command 10)
/-- There are interpretations of the declared symbols satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Prop),
  ∃ (r1 : Int → Int → Int → Prop),
  (∀ (A B C D E F G H : Int),
  (r1 F E B) →
  (((0 : Int) = D) = ((0 : Int) ≤ C)) →
  (((0 : Int) = H) = (B ≤ (2 : Int))) →
  ((0 : Int) = G) →
  ((0 : Int) = D) →
  (¬(0 : Int) = H) →
  (E = (-1 : Int) + C) →
  (A = F) →
  (((0 : Int) = G) = ((1 : Int) ≤ B)) →
  r1 A C B) ∧
  ((∀ (A B C D E F G H : Int),
  (r1 G F E) →
  (((0 : Int) = H) = ((1 : Int) ≤ B)) →
  ((0 : Int) = D) →
  (¬(0 : Int) = H) →
  (F = (-1 : Int) + C) →
  (E = (-1 : Int) + B) →
  (A = G) →
  (((0 : Int) = D) = ((0 : Int) ≤ C)) →
  r1 A C B) ∧
  ((∀ (A B C D E F G H I : Int),
  (r1 I H G) →
  (((0 : Int) = E) = ((1 : Int) ≤ B)) →
  (((0 : Int) = D) = ((0 : Int) ≤ C)) →
  ((0 : Int) = F) →
  ((0 : Int) = E) →
  ((0 : Int) = D) →
  (A = I) →
  (H = (-1 : Int) + C) →
  (G = (3 : Int) + (-1 : Int) * B) →
  (((0 : Int) = F) = (B ≤ (2 : Int))) →
  r1 A C B) ∧
  ((∀ (A B C D : Int),
  (¬(0 : Int) = D) →
  (A = B) →
  (((0 : Int) = D) = ((0 : Int) ≤ C)) →
  r1 A C B) ∧
  ((∀ (A B C D E F G H : Int),
  (r1 G A F) →
  (r1 D A C) →
  (¬((0 : Int) = H) = (G ≥ (3 : Int))) →
  ((0 : Int) = E) →
  (¬(0 : Int) = H) →
  (F = (3 : Int)) →
  (C = (1 : Int)) →
  (B = (1 : Int)) →
  (¬((0 : Int) = E) = (D ≥ (0 : Int))) →
  r0) ∧
  ((∀ (A B C D : Int),
  (r1 C A B) →
  ((0 : Int) = D) →
  (B = (3 : Int)) →
  (¬((0 : Int) = D) = (C ≥ (3 : Int))) →
  r0) ∧
  (∀ (_CHC_COMP_UNUSED : Prop),
  (r0) →
  False))))))

end

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of a satisfying interpretation.
theorem problem : Problem := by
  sorry

end «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive_000»

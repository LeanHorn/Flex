import Init

set_option maxRecDepth 4096

namespace «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive4_000»

-- Statements

section
set_option Elab.async false

-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":124:1-124:12 (check-sat, command 14)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":8:1-18:2 (clause 1, command 5)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":19:1-33:2 (clause 2, command 6)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":34:1-48:2 (clause 3, command 7)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":49:1-59:2 (clause 4, command 8)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":60:1-74:2 (clause 5, command 9)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":75:1-85:2 (clause 6, command 10)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":86:1-101:2 (clause 7, command 11)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":102:1-111:2 (clause 8, command 12)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/inductive4_000.smt2":112:1-122:2 (clause 9, command 13)
/-- There are interpretations of the declared symbols satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Int → Int → Prop),
  ∃ (r1 : Int → Int → Prop),
  ∃ (r2 : Int → Int → Prop),
  (∀ (A B C D E : Int),
  (r0 A B) →
  (¬(0 : Int) = D) →
  (E = (-4 : Int)) →
  (((0 : Int) = D) = ((-3 : Int) ≤ C)) →
  r0 A B) ∧
  ((∀ (A B C D E F : Int),
  (r0 A B) →
  (((0 : Int) = D) = ((-3 : Int) ≤ C)) →
  ((0 : Int) = E) →
  ((0 : Int) = D) →
  (F = (-2 : Int) + C) →
  (¬((0 : Int) = E) = (C ≤ (1 : Int))) →
  r0 A B) ∧
  ((∀ (A B C D E F : Int),
  (r2 A E) →
  (¬((0 : Int) = D) = (B ≤ (1 : Int))) →
  ((0 : Int) = C) →
  ((0 : Int) = D) →
  (F = (-2 : Int) + B) →
  (((0 : Int) = C) = ((-3 : Int) ≤ B)) →
  r0 A E) ∧
  ((∀ (A B C : Int),
  (r1 A C) →
  (B = (3 : Int)) →
  r0 A C) ∧
  ((∀ (A B C D E : Int),
  (r0 E B) →
  (((0 : Int) = C) = ((-3 : Int) ≤ B)) →
  (¬(0 : Int) = D) →
  ((0 : Int) = C) →
  (A = E) →
  (¬((0 : Int) = D) = (B ≤ (1 : Int))) →
  r2 A B) ∧
  ((∀ (A B C D E : Int),
  (r2 E D) →
  (¬(0 : Int) = C) →
  (A = E) →
  (D = (-4 : Int)) →
  (((0 : Int) = C) = ((-3 : Int) ≤ B)) →
  r2 A B) ∧
  ((∀ (A B C D E F : Int),
  (r2 F E) →
  (¬((0 : Int) = D) = (B ≤ (1 : Int))) →
  ((0 : Int) = C) →
  ((0 : Int) = D) →
  (A = F) →
  (E = (-2 : Int) + B) →
  (((0 : Int) = C) = ((-3 : Int) ≤ B)) →
  r2 A B) ∧
  ((∀ (A B : Int),
  (A = (1 : Int) + B) →
  r1 A B) ∧
  (∀ (A B C : Int),
  (r2 B A) →
  ((0 : Int) = C) →
  (A = (3 : Int)) →
  (¬((0 : Int) = C) = (B ≥ (-3 : Int))) →
  False))))))))

end

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of a satisfying interpretation.
theorem problem : Problem := by
  sorry

end «Smt2Lean».«Generated».«hopv».«lia».«fpice».«inductive4_000»

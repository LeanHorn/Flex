import Init

set_option maxRecDepth 4096

namespace «Smt2Lean».«Generated».«hopv».«lia».«fpice».«repeat_000»

-- Statements

section
set_option Elab.async false

-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":74:1-74:12 (check-sat, command 11)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":8:1-18:2 (clause 1, command 5)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":19:1-29:2 (clause 2, command 6)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":30:1-41:2 (clause 3, command 7)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":42:1-51:2 (clause 4, command 8)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":52:1-61:2 (clause 5, command 9)
-- Source: "/Users/jamkabeeralikhan/Documents/Programming/Flex/evaluation/CHC-COMP/sources/hopv/lia/fpice/repeat_000.smt2":62:1-72:2 (clause 6, command 10)
/-- There are interpretations of the declared symbols satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Int → Int → Prop),
  ∃ (r1 : Int → Int → Prop),
  ∃ (r2 : Int → Int → Int → Prop),
  (∀ (A B C D E : Int),
  (r0 A B) →
  ((0 : Int) = D) →
  (E = (-1 : Int) + C) →
  (¬((0 : Int) = D) = (C = (0 : Int))) →
  r0 A B) ∧
  ((∀ (A B C : Int),
  (r1 A C) →
  (B = (0 : Int)) →
  r0 A C) ∧
  ((∀ (A B C D E F G : Int),
  (r0 G F) →
  (r2 F C E) →
  ((0 : Int) = D) →
  (A = G) →
  (E = (-1 : Int) + B) →
  (¬((0 : Int) = D) = (B = (0 : Int))) →
  r2 A C B) ∧
  ((∀ (A B C D : Int),
  (¬(0 : Int) = D) →
  (A = C) →
  (¬((0 : Int) = D) = (B = (0 : Int))) →
  r2 A C B) ∧
  ((∀ (A B : Int),
  (A = (1 : Int) + B) →
  r1 A B) ∧
  (∀ (A B C D : Int),
  (r2 C B A) →
  ((0 : Int) = D) →
  (B = (0 : Int)) →
  (¬((0 : Int) = D) = (C ≥ A)) →
  False)))))

end

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of a satisfying interpretation.
theorem problem : Problem := by
  sorry

end «Smt2Lean».«Generated».«hopv».«lia».«fpice».«repeat_000»

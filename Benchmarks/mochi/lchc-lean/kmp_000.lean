import Flex.Tactic
import Flex.CHC

/-! KMP from CHC-COMP hopv/lia/mochi: 30 predicates, 89 clauses.
Zap removes 15 predicates; explicit arithmetic invariants complete the proof. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace MochiKmp

section
set_option Elab.async false

/-- The original CHCs, with one existential per declared predicate. -/
def Problem : Prop :=
  ∃ (r0 : Int → Int → Prop),
  ∃ (r1 : Int → Int → Int → Int → Prop),
  ∃ (r2 : Int → Int → Int → Int → Prop),
  ∃ (r3 : Int → Int → Int → Int → Int → Int → Prop),
  ∃ (r4 : Int → Int → Int → Int → Int → Prop),
  ∃ (r5 : Int → Int → Int → Prop),
  ∃ (r6 : Int → Int → Int → Int → Int → Prop),
  ∃ (r7 : Int → Int → Prop),
  ∃ (r8 : Int → Int → Int → Prop),
  ∃ (r9 : Int → Int → Int → Int → Prop),
  ∃ (r10 : Int → Int → Int → Int → Prop),
  ∃ (r11 : Int → Int → Int → Prop),
  ∃ (r12 : Int → Int → Int → Prop),
  ∃ (r13 : Int → Int → Int → Prop),
  ∃ (r14 : Int → Int → Int → Prop),
  ∃ (r15 : Int → Int → Int → Int → Prop),
  ∃ (r16 : Int → Int → Int → Int → Int → Int → Prop),
  ∃ (r17 : Int → Int → Int → Int → Int → Prop),
  ∃ (r18 : Int → Int → Int → Int → Prop),
  ∃ (r19 : Int → Int → Int → Prop),
  ∃ (r20 : Int → Int → Int → Prop),
  ∃ (r21 : Int → Int → Int → Prop),
  ∃ (r22 : Int → Int → Int → Int → Int → Prop),
  ∃ (r23 : Int → Int → Int → Prop),
  ∃ (r24 : Int → Int → Int → Int → Prop),
  ∃ (r25 : Int → Int → Int → Int → Prop),
  ∃ (r26 : Int → Int → Int → Int → Prop),
  ∃ (r27 : Int → Int → Int → Int → Prop),
  ∃ (r28 : Int → Int → Prop),
  ∃ (r29 : Int → Int → Int → Int → Int → Int → Prop),
  (((((((∀ (A B C D E F G H : Int),
  (r26 H F C B) →
  (r17 F E D C B) →
  ((0 : Int) = G) →
  (A = H) →
  (¬((0 : Int) = G) = (B = F)) →
  r3 A F E D C B) ∧
  (∀ (A B C D E F G : Int),
  (r17 F E D C B) →
  (¬(0 : Int) = G) →
  (A = D) →
  (¬((0 : Int) = G) = (B = F)) →
  r3 A F E D C B)) ∧
  ((∀ (A B C D E F : Int),
  (r17 E D C B A) →
  ((0 : Int) = F) →
  (¬((0 : Int) = F) = (A = E)) →
  r13 E B A) ∧
  (∀ (A B C D E v_5 : Int),
  (r13 A C B) →
  (r11 D C B) →
  (r2 E B C v_5) →
  (v_5 = B) →
  r19 A C B))) ∧
  (((∀ (A B C v_3 : Int),
  (r11 C B A) →
  (v_3 = A) →
  r19 A B v_3) ∧
  (∀ (A B C D E F v_6 : Int),
  (r13 D C B) →
  (r11 E C B) →
  (r2 F B C v_6) →
  (r2 A D C B) →
  (v_6 = B) →
  r26 A D C B)) ∧
  ((∀ (A B C D E F v_6 : Int),
  (r3 B A F E D C) →
  (r18 A E D C) →
  (r11 E D C) →
  (r2 F C D v_6) →
  (v_6 = C) →
  r22 B A E D C) ∧
  (∀ (A B C D E F G H : Int),
  (r28 A B) →
  (r0 C B) →
  (G = (1 : Int)) →
  (F = (-1 : Int)) →
  (E = (0 : Int)) →
  (D = (0 : Int)) →
  (H = (-1 : Int)) →
  r7 A B)))) ∧
  ((((∀ (A B C D E F G H I J K L M N O P v_16 : Int),
  (r8 A C B) →
  (r27 G E C B) →
  (r29 L E v_16 D C B) →
  (r15 E D C B) →
  (r27 I H C B) →
  (v_16 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  (¬(0 : Int) = O) →
  ((0 : Int) = K) →
  (H = (1 : Int) + D) →
  (P = (1 : Int) + D) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (¬((0 : Int) = F) = (E = C)) →
  r8 A C B) ∧
  (∀ (A B C D E F G H I J K L M N O v_15 : Int),
  (r8 A C B) →
  (r27 G E C B) →
  (r29 L E v_15 D C B) →
  (r15 E D C B) →
  (r27 I H C B) →
  (v_15 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  ((0 : Int) = O) →
  ((0 : Int) = K) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r8 A C B)) ∧
  ((∀ (A B C D E F G H I J K L M v_13 : Int),
  (r8 A C B) →
  (r27 G E C B) →
  (r29 M D E v_13 C B) →
  (r15 E D C B) →
  (r27 I H C B) →
  (v_13 = D) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  (¬((0 : Int) = F) = (E = C)) →
  (¬(0 : Int) = L) →
  (¬(0 : Int) = K) →
  ((0 : Int) = F) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = L) = (D ≥ (0 : Int))) →
  r8 A C B) ∧
  (∀ (A B C D E F G H I J K L M N : Int),
  (r8 A C B) →
  (r27 G E C B) →
  (r15 E D C B) →
  (r27 I H C B) →
  (¬((0 : Int) = L) = (D ≥ (0 : Int))) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  ((0 : Int) = L) →
  (¬(0 : Int) = K) →
  (N = (1 : Int) + E) →
  (M = (-1 : Int)) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r8 A C B))) ∧
  (((∀ (A B C D E F G : Int),
  (r27 F D B A) →
  (r15 D C B A) →
  ((0 : Int) = E) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = E) = (D = B)) →
  r8 G B A) ∧
  (∀ (A B C D E : Int),
  (r15 D C B A) →
  ((0 : Int) = E) →
  (¬((0 : Int) = E) = (D = B)) →
  r8 D B A)) ∧
  ((∀ (A B C D E F G H I J K L M N O P Q v_17 : Int),
  (r8 D C B) →
  (r27 A D C B) →
  (r29 M F v_17 E C B) →
  (r15 F E C B) →
  (r27 H F C B) →
  (r27 J I C B) →
  (v_17 = F) →
  (((0 : Int) = P) = (F ≤ O)) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  (¬(0 : Int) = P) →
  ((0 : Int) = L) →
  (I = (1 : Int) + E) →
  (Q = (1 : Int) + E) →
  (O = (1 : Int) + E) →
  (N = (1 : Int) + F) →
  (¬((0 : Int) = G) = (F = C)) →
  r27 A D C B) ∧
  (∀ (A B C D E F G H I J K L M N O P v_16 : Int),
  (r8 D C B) →
  (r27 A D C B) →
  (r29 M F v_16 E C B) →
  (r15 F E C B) →
  (r27 H F C B) →
  (r27 J I C B) →
  (v_16 = F) →
  (((0 : Int) = P) = (F ≤ O)) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  ((0 : Int) = P) →
  ((0 : Int) = L) →
  (O = (1 : Int) + E) →
  (N = (1 : Int) + F) →
  (I = (1 : Int) + E) →
  (¬((0 : Int) = G) = (F = C)) →
  r27 A D C B))))) ∧
  (((((∀ (A B C D E F G H I J K L M N v_14 : Int),
  (r8 D C B) →
  (r27 A D C B) →
  (r29 N E F v_14 C B) →
  (r15 F E C B) →
  (r27 H F C B) →
  (r27 J I C B) →
  (v_14 = E) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  (¬((0 : Int) = G) = (F = C)) →
  (¬(0 : Int) = M) →
  (¬(0 : Int) = L) →
  ((0 : Int) = G) →
  (I = (1 : Int) + E) →
  (¬((0 : Int) = M) = (E ≥ (0 : Int))) →
  r27 A D C B) ∧
  (∀ (A B C D E F G H I J K L M N O : Int),
  (r8 D C B) →
  (r27 A D C B) →
  (r15 F E C B) →
  (r27 H F C B) →
  (r27 J I C B) →
  (¬((0 : Int) = M) = (E ≥ (0 : Int))) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  ((0 : Int) = M) →
  (¬(0 : Int) = L) →
  (O = (1 : Int) + F) →
  (N = (-1 : Int)) →
  (I = (1 : Int) + E) →
  (¬((0 : Int) = G) = (F = C)) →
  r27 A D C B)) ∧
  ((∀ (A B C D E F G : Int),
  (r8 D C B) →
  (r25 A D C B) →
  (r0 C B) →
  (F = (1 : Int)) →
  (E = (-1 : Int)) →
  (G = (-1 : Int)) →
  r27 A D C B) ∧
  (∀ (A B C D E F G H I J K L M v_13 : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r29 M D E v_13 C B) →
  (r6 A E M C B) →
  (r15 E D C B) →
  (v_13 = D) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  (¬((0 : Int) = F) = (E = C)) →
  (¬(0 : Int) = L) →
  (¬(0 : Int) = K) →
  ((0 : Int) = F) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = L) = (D ≥ (0 : Int))) →
  r6 A E D C B))) ∧
  (((∀ (A B C D E F G H I J K L M N O v_15 : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r29 L E v_15 D C B) →
  (r6 A M L C B) →
  (r15 E D C B) →
  (v_15 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  ((0 : Int) = O) →
  ((0 : Int) = K) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r6 A E D C B) ∧
  (∀ (A B C D E F G H I J K L M N : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r6 A N M C B) →
  (r15 E D C B) →
  (¬((0 : Int) = L) = (D ≥ (0 : Int))) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  ((0 : Int) = L) →
  (¬(0 : Int) = K) →
  (N = (1 : Int) + E) →
  (M = (-1 : Int)) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r6 A E D C B)) ∧
  ((∀ (A B C D E F G H I J K L M N : Int),
  (r27 G E C B) →
  (r19 A C E) →
  (r27 I H C B) →
  (r15 E D C B) →
  (((0 : Int) = M) = (E ≤ L)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  (¬(0 : Int) = M) →
  ((0 : Int) = K) →
  (N = (1 : Int) + D) →
  (L = (1 : Int) + D) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r6 A E D C B) ∧
  (∀ (A B C D E F G H I J K v_11 : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r15 D C B A) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  (¬((0 : Int) = E) = (D = B)) →
  (¬(0 : Int) = K) →
  (¬(0 : Int) = J) →
  ((0 : Int) = E) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = K) = (C ≥ (0 : Int))) →
  (v_11 = C) →
  r6 C D v_11 B A)))) ∧
  ((((∀ (A B C D E F G H I J K L M N v_14 : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r15 D C B A) →
  (((0 : Int) = M) = (D ≤ L)) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  ((0 : Int) = E) →
  (¬(0 : Int) = M) →
  ((0 : Int) = J) →
  (N = (1 : Int) + C) →
  (L = (1 : Int) + C) →
  (K = (1 : Int) + D) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = E) = (D = B)) →
  (v_14 = D) →
  r6 D v_14 C B A) ∧
  (∀ (A B C D E F G H I J K L M v_13 : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r15 D C B A) →
  (((0 : Int) = M) = (D ≤ L)) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  ((0 : Int) = E) →
  ((0 : Int) = M) →
  ((0 : Int) = J) →
  (L = (1 : Int) + C) →
  (K = (1 : Int) + D) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = E) = (D = B)) →
  (v_13 = D) →
  r6 D v_13 C B A)) ∧
  ((∀ (A B C D E F : Int),
  (r15 E D C B) →
  (r4 A E D C B) →
  (¬(0 : Int) = F) →
  (¬((0 : Int) = F) = (E = C)) →
  r6 A E D C B) ∧
  (∀ (A B C D E F G H I J K L M N O P v_16 : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r29 L E v_16 D C B) →
  (r6 A M L C B) →
  (r15 E D C B) →
  (v_16 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  (¬(0 : Int) = O) →
  ((0 : Int) = K) →
  (H = (1 : Int) + D) →
  (P = (1 : Int) + D) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (¬((0 : Int) = F) = (E = C)) →
  r18 A P C E))) ∧
  (((∀ (A B C D E F G H I J K L M N v_14 : Int),
  (r27 H E C B) →
  (r27 J I C B) →
  (r29 N D E v_14 C B) →
  (r29 A F E D C B) →
  (r6 F E N C B) →
  (r15 E D C B) →
  (v_14 = D) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  (¬((0 : Int) = G) = (E = C)) →
  (¬(0 : Int) = M) →
  (¬(0 : Int) = L) →
  ((0 : Int) = G) →
  (I = (1 : Int) + D) →
  (¬((0 : Int) = M) = (D ≥ (0 : Int))) →
  r29 A F E N C B) ∧
  (∀ (A B C D E F G H I J K L M N O P v_16 : Int),
  (r27 H E C B) →
  (r27 J I C B) →
  (r29 M E v_16 D C B) →
  (r29 A F E D C B) →
  (r6 F N M C B) →
  (r15 E D C B) →
  (v_16 = E) →
  (((0 : Int) = P) = (E ≤ O)) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  ((0 : Int) = P) →
  ((0 : Int) = L) →
  (O = (1 : Int) + D) →
  (N = (1 : Int) + E) →
  (I = (1 : Int) + D) →
  (¬((0 : Int) = G) = (E = C)) →
  r29 A F N M C B)) ∧
  ((∀ (A B C D E F G H I J K L M N O : Int),
  (r27 H E C B) →
  (r27 J I C B) →
  (r29 A F E D C B) →
  (r6 F O N C B) →
  (r15 E D C B) →
  (¬((0 : Int) = M) = (D ≥ (0 : Int))) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  ((0 : Int) = M) →
  (¬(0 : Int) = L) →
  (O = (1 : Int) + E) →
  (N = (-1 : Int)) →
  (I = (1 : Int) + D) →
  (¬((0 : Int) = G) = (E = C)) →
  r29 A F O N C B) ∧
  (∀ (A B C D E F G H I J K L M N O P Q v_17 : Int),
  (r27 G E C B) →
  (r22 A Q P C E) →
  (r27 I H C B) →
  (r29 L E v_17 D C B) →
  (r6 Q M L C B) →
  (r15 E D C B) →
  (v_17 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  (¬(0 : Int) = O) →
  ((0 : Int) = K) →
  (H = (1 : Int) + D) →
  (P = (1 : Int) + D) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (¬((0 : Int) = F) = (E = C)) →
  r29 A Q M L C B)))))) ∧
  ((((((∀ (A B C D E F G : Int),
  (r6 G E D C B) →
  (r10 A G F C) →
  (r0 C B) →
  (E = (1 : Int)) →
  (D = (-1 : Int)) →
  (F = (-1 : Int)) →
  r29 A G E D C B) ∧
  (∀ (A B C D E F G H I J K L M N O : Int),
  (r27 H E C B) →
  (r19 F C E) →
  (r27 J I C B) →
  (r29 A F E D C B) →
  (r15 E D C B) →
  (((0 : Int) = N) = (E ≤ M)) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  (¬(0 : Int) = N) →
  ((0 : Int) = L) →
  (O = (1 : Int) + D) →
  (M = (1 : Int) + D) →
  (I = (1 : Int) + D) →
  (¬((0 : Int) = G) = (E = C)) →
  r2 A F C E)) ∧
  ((∀ (A B C D E F G H I J K L M N O P v_16 : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r4 A E D C B) →
  (r29 L E v_16 D C B) →
  (r15 E D C B) →
  (v_16 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  (¬(0 : Int) = O) →
  ((0 : Int) = K) →
  (H = (1 : Int) + D) →
  (P = (1 : Int) + D) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (¬((0 : Int) = F) = (E = C)) →
  r4 A M L C B) ∧
  (∀ (A B C D E F G H I J K L M N O v_15 : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r4 A E D C B) →
  (r29 L E v_15 D C B) →
  (r15 E D C B) →
  (v_15 = E) →
  (((0 : Int) = O) = (E ≤ N)) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  ((0 : Int) = O) →
  ((0 : Int) = K) →
  (N = (1 : Int) + D) →
  (M = (1 : Int) + E) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r4 A M L C B))) ∧
  (((∀ (A B C D E F G H I J K L M v_13 : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r4 A E D C B) →
  (r29 M D E v_13 C B) →
  (r15 E D C B) →
  (v_13 = D) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  (¬((0 : Int) = F) = (E = C)) →
  (¬(0 : Int) = L) →
  (¬(0 : Int) = K) →
  ((0 : Int) = F) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = L) = (D ≥ (0 : Int))) →
  r4 A E M C B) ∧
  (∀ (A B C D E F G H I J K L M N : Int),
  (r27 G E C B) →
  (r27 I H C B) →
  (r4 A E D C B) →
  (r15 E D C B) →
  (¬((0 : Int) = L) = (D ≥ (0 : Int))) →
  (¬((0 : Int) = K) = ((0 : Int) = J)) →
  (¬((0 : Int) = J) = (G = I)) →
  ((0 : Int) = F) →
  ((0 : Int) = L) →
  (¬(0 : Int) = K) →
  (N = (1 : Int) + E) →
  (M = (-1 : Int)) →
  (H = (1 : Int) + D) →
  (¬((0 : Int) = F) = (E = C)) →
  r4 A N M C B)) ∧
  ((∀ (A B C D E F G H : Int),
  (r21 A C B) →
  (r0 C B) →
  (G = (1 : Int)) →
  (F = (-1 : Int)) →
  (E = (0 : Int)) →
  (D = (0 : Int)) →
  (H = (-1 : Int)) →
  r4 A G F C B) ∧
  (∀ (A B C D E F G H I J K L M N O P Q v_17 : Int),
  (r27 H F D C) →
  (r27 J I D C) →
  (r16 B A N M D C) →
  (r4 A F E D C) →
  (r29 M F v_17 E D C) →
  (r15 F E D C) →
  (v_17 = F) →
  (((0 : Int) = P) = (F ≤ O)) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  (¬(0 : Int) = P) →
  ((0 : Int) = L) →
  (I = (1 : Int) + E) →
  (Q = (1 : Int) + E) →
  (O = (1 : Int) + E) →
  (N = (1 : Int) + F) →
  (¬((0 : Int) = G) = (F = D)) →
  r16 B A F E D C)))) ∧
  ((((∀ (A B C D E F G H I J K L M N O P v_16 : Int),
  (r27 H F D C) →
  (r27 J I D C) →
  (r16 B A N M D C) →
  (r4 A F E D C) →
  (r29 M F v_16 E D C) →
  (r15 F E D C) →
  (v_16 = F) →
  (((0 : Int) = P) = (F ≤ O)) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  ((0 : Int) = P) →
  ((0 : Int) = L) →
  (O = (1 : Int) + E) →
  (N = (1 : Int) + F) →
  (I = (1 : Int) + E) →
  (¬((0 : Int) = G) = (F = D)) →
  r16 B A F E D C) ∧
  (∀ (A B C D E F G H I J K L M N v_14 : Int),
  (r27 H F D C) →
  (r27 J I D C) →
  (r16 B A F N D C) →
  (r4 A F E D C) →
  (r29 N E F v_14 D C) →
  (r15 F E D C) →
  (v_14 = E) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  (¬((0 : Int) = G) = (F = D)) →
  (¬(0 : Int) = M) →
  (¬(0 : Int) = L) →
  ((0 : Int) = G) →
  (I = (1 : Int) + E) →
  (¬((0 : Int) = M) = (E ≥ (0 : Int))) →
  r16 B A F E D C)) ∧
  ((∀ (A B C D E F G H I J K L M N O : Int),
  (r27 H F D C) →
  (r27 J I D C) →
  (r16 B A O N D C) →
  (r4 A F E D C) →
  (r15 F E D C) →
  (¬((0 : Int) = M) = (E ≥ (0 : Int))) →
  (¬((0 : Int) = L) = ((0 : Int) = K)) →
  (¬((0 : Int) = K) = (H = J)) →
  ((0 : Int) = G) →
  ((0 : Int) = M) →
  (¬(0 : Int) = L) →
  (O = (1 : Int) + F) →
  (N = (-1 : Int)) →
  (I = (1 : Int) + E) →
  (¬((0 : Int) = G) = (F = D)) →
  r16 B A F E D C) ∧
  (∀ (A B C D E F G : Int),
  (r15 F E D C) →
  (r29 B A F E D C) →
  (r4 A F E D C) →
  (¬(0 : Int) = G) →
  (¬((0 : Int) = G) = (F = D)) →
  r16 B A F E D C))) ∧
  (((∀ (A B C D E F G H I J K L M N O v_15 : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r29 K D v_15 C B A) →
  (r15 D C B A) →
  (v_15 = D) →
  (((0 : Int) = N) = (D ≤ M)) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  ((0 : Int) = E) →
  (¬(0 : Int) = N) →
  ((0 : Int) = J) →
  (G = (1 : Int) + C) →
  (O = (1 : Int) + C) →
  (M = (1 : Int) + C) →
  (L = (1 : Int) + D) →
  (¬((0 : Int) = E) = (D = B)) →
  r15 L K B A) ∧
  (∀ (A B C D E F G H I J K L M N v_14 : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r29 K D v_14 C B A) →
  (r15 D C B A) →
  (v_14 = D) →
  (((0 : Int) = N) = (D ≤ M)) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  ((0 : Int) = E) →
  ((0 : Int) = N) →
  ((0 : Int) = J) →
  (M = (1 : Int) + C) →
  (L = (1 : Int) + D) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = E) = (D = B)) →
  r15 L K B A)) ∧
  ((∀ (A B C D E F G H I J K L v_12 : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r29 L C D v_12 B A) →
  (r15 D C B A) →
  (v_12 = C) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  (¬((0 : Int) = E) = (D = B)) →
  (¬(0 : Int) = K) →
  (¬(0 : Int) = J) →
  ((0 : Int) = E) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = K) = (C ≥ (0 : Int))) →
  r15 D L B A) ∧
  (∀ (A B C D E F G H I J K L M : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r15 D C B A) →
  (¬((0 : Int) = K) = (C ≥ (0 : Int))) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  ((0 : Int) = E) →
  ((0 : Int) = K) →
  (¬(0 : Int) = J) →
  (M = (1 : Int) + D) →
  (L = (-1 : Int)) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = E) = (D = B)) →
  r15 M L B A))))) ∧
  (((((∀ (A B C D E : Int),
  (r0 B A) →
  (D = (1 : Int)) →
  (C = (-1 : Int)) →
  (E = (-1 : Int)) →
  r15 D C B A) ∧
  (∀ (A B C D E F G H I J K L M : Int),
  (r27 F D B A) →
  (r27 H G B A) →
  (r15 D C B A) →
  (((0 : Int) = L) = (D ≤ K)) →
  (¬((0 : Int) = J) = ((0 : Int) = I)) →
  (¬((0 : Int) = I) = (F = H)) →
  ((0 : Int) = E) →
  (¬(0 : Int) = L) →
  ((0 : Int) = J) →
  (M = (1 : Int) + C) →
  (K = (1 : Int) + C) →
  (G = (1 : Int) + C) →
  (¬((0 : Int) = E) = (D = B)) →
  r11 M B D)) ∧
  ((∀ (A B C D E F : Int),
  (r8 A C B) →
  (r0 C B) →
  (E = (1 : Int)) →
  (D = (-1 : Int)) →
  (F = (-1 : Int)) →
  r20 A C B) ∧
  (∀ (A B C D E F G H : Int),
  (r12 A C B) →
  (r0 C B) →
  (G = (1 : Int)) →
  (F = (-1 : Int)) →
  (E = (0 : Int)) →
  (D = (0 : Int)) →
  (H = (-1 : Int)) →
  r20 A C B))) ∧
  (((∀ (A B C D E F : Int),
  (r6 A E D C B) →
  (r0 C B) →
  (E = (1 : Int)) →
  (D = (-1 : Int)) →
  (F = (-1 : Int)) →
  r5 A F C) ∧
  (∀ (A B C D E F G : Int),
  let a!1 := ((0 : Int) = G) = (¬(0 : Int) = E ∧ ¬(0 : Int) = F);
  r7 A B → ((0 : Int) = F) = (D ≤ (0 : Int)) → ((0 : Int) = E) = (B ≤ (0 : Int)) → ¬(0 : Int) = G → ¬a!1 → r5 A C B)) ∧
  ((∀ (A B C D E F G : Int),
  let a!1 := ((0 : Int) = G) = (¬(0 : Int) = E ∧ ¬(0 : Int) = F);
  r20 A C B → ((0 : Int) = F) = (C ≤ (0 : Int)) → ((0 : Int) = E) = (B ≤ (0 : Int)) → ¬(0 : Int) = G → ¬a!1 → r5 A D C) ∧
  (∀ (A B C D E F G H I : Int),
  (r16 A H G F C B) →
  (r0 C B) →
  (r21 H C B) →
  (G = (1 : Int)) →
  (F = (-1 : Int)) →
  (E = (0 : Int)) →
  (D = (0 : Int)) →
  (I = (-1 : Int)) →
  r1 A H C B)))) ∧
  ((((∀ (A B C D E F G H I J K L M N O : Int),
  (r14 I E B) →
  (r24 F E C B) →
  (r9 J F C B) →
  (r1 N M C B) →
  (r1 A D C B) →
  (r21 D C B) →
  (¬((0 : Int) = L) = (F = (0 : Int))) →
  (¬((0 : Int) = K) = (I = J)) →
  (((0 : Int) = H) = (B ≤ E)) →
  (¬(0 : Int) = G) →
  ((0 : Int) = L) →
  ((0 : Int) = K) →
  (¬(0 : Int) = H) →
  (O = (1 : Int) + N) →
  (M = (-1 : Int) + F) →
  (((0 : Int) = G) = (C ≤ F)) →
  r1 A D C B) ∧
  (∀ (A B C D E F G H I J K L M : Int),
  (r14 K E B) →
  (r24 F E C B) →
  (r9 L F C B) →
  (r1 A D C B) →
  (r21 D C B) →
  (((0 : Int) = J) = (B ≤ E)) →
  (((0 : Int) = I) = (C ≤ F)) →
  (¬(0 : Int) = M) →
  (¬(0 : Int) = J) →
  (¬(0 : Int) = I) →
  (H = (1 : Int) + F) →
  (G = (1 : Int) + E) →
  (¬((0 : Int) = M) = (K = L)) →
  r1 A D C B)) ∧
  ((∀ (A B C D E F G H I J K L M : Int),
  (r14 J E B) →
  (r24 F E C B) →
  (r9 K F C B) →
  (r1 A D C B) →
  (r21 D C B) →
  (¬((0 : Int) = L) = (J = K)) →
  (((0 : Int) = I) = (B ≤ E)) →
  (((0 : Int) = H) = (C ≤ F)) →
  (¬(0 : Int) = M) →
  ((0 : Int) = L) →
  (¬(0 : Int) = I) →
  (¬(0 : Int) = H) →
  (G = (1 : Int) + E) →
  (¬((0 : Int) = M) = (F = (0 : Int))) →
  r1 A D C B) ∧
  (∀ (A B C D E F G H I J K L M N : Int),
  (r28 A B) →
  (r24 E D C B) →
  (r14 H D B) →
  (r1 M L C B) →
  (r9 I E C B) →
  (¬((0 : Int) = K) = (E = (0 : Int))) →
  (¬((0 : Int) = J) = (H = I)) →
  (((0 : Int) = G) = (B ≤ D)) →
  (¬(0 : Int) = F) →
  ((0 : Int) = K) →
  ((0 : Int) = J) →
  (¬(0 : Int) = G) →
  (N = (1 : Int) + M) →
  (L = (-1 : Int) + E) →
  (((0 : Int) = F) = (C ≤ E)) →
  r28 A B))) ∧
  (((∀ (A B C D E F G H I J K L : Int),
  (r28 A B) →
  (r24 E D C B) →
  (r14 J D B) →
  (r9 K E C B) →
  (((0 : Int) = I) = (B ≤ D)) →
  (((0 : Int) = H) = (C ≤ E)) →
  (¬(0 : Int) = L) →
  (¬(0 : Int) = I) →
  (¬(0 : Int) = H) →
  (G = (1 : Int) + E) →
  (F = (1 : Int) + D) →
  (¬((0 : Int) = L) = (J = K)) →
  r28 A B) ∧
  (∀ (A B C D E F G H I J K L : Int),
  (r28 A B) →
  (r24 E D C B) →
  (r14 I D B) →
  (r9 J E C B) →
  (¬((0 : Int) = K) = (I = J)) →
  (((0 : Int) = H) = (B ≤ D)) →
  (((0 : Int) = G) = (C ≤ E)) →
  (¬(0 : Int) = L) →
  ((0 : Int) = K) →
  (¬(0 : Int) = H) →
  (¬(0 : Int) = G) →
  (F = (1 : Int) + D) →
  (¬((0 : Int) = L) = (E = (0 : Int))) →
  r28 A B)) ∧
  ((∀ (A B C D E F : Int),
  (r24 D C B A) →
  (((0 : Int) = E) = (B ≤ D)) →
  (¬(0 : Int) = F) →
  (¬(0 : Int) = E) →
  (((0 : Int) = F) = (A ≤ C)) →
  r28 C A) ∧
  (∀ (A B C D E F G H I J K L M N O : Int),
  (r28 C B) →
  (r24 F E D B) →
  (r14 A C B) →
  (r1 N M D B) →
  (r9 J F D B) →
  (r14 I E B) →
  (¬((0 : Int) = L) = (F = (0 : Int))) →
  (¬((0 : Int) = K) = (I = J)) →
  (((0 : Int) = H) = (B ≤ E)) →
  (¬(0 : Int) = G) →
  ((0 : Int) = L) →
  ((0 : Int) = K) →
  (¬(0 : Int) = H) →
  (O = (1 : Int) + N) →
  (M = (-1 : Int) + F) →
  (((0 : Int) = G) = (D ≤ F)) →
  r14 A C B))))))) ∧
  ((((((∀ (A B C D E F G H I J K L M : Int),
  (r28 C B) →
  (r24 F E D B) →
  (r14 A C B) →
  (r9 L F D B) →
  (r14 K E B) →
  (((0 : Int) = J) = (B ≤ E)) →
  (((0 : Int) = I) = (D ≤ F)) →
  (¬(0 : Int) = M) →
  (¬(0 : Int) = J) →
  (¬(0 : Int) = I) →
  (H = (1 : Int) + F) →
  (G = (1 : Int) + E) →
  (¬((0 : Int) = M) = (K = L)) →
  r14 A C B) ∧
  (∀ (A B C D E F G H I J K L M : Int),
  (r28 C B) →
  (r24 F E D B) →
  (r14 A C B) →
  (r9 K F D B) →
  (r14 J E B) →
  (¬((0 : Int) = L) = (J = K)) →
  (((0 : Int) = I) = (B ≤ E)) →
  (((0 : Int) = H) = (D ≤ F)) →
  (¬(0 : Int) = M) →
  ((0 : Int) = L) →
  (¬(0 : Int) = I) →
  (¬(0 : Int) = H) →
  (G = (1 : Int) + E) →
  (¬((0 : Int) = M) = (F = (0 : Int))) →
  r14 A C B)) ∧
  ((∀ (A B C D E F G H I : Int),
  (r28 C B) →
  (r0 D B) →
  (r23 A C B) →
  (H = (1 : Int)) →
  (G = (-1 : Int)) →
  (F = (0 : Int)) →
  (E = (0 : Int)) →
  (I = (-1 : Int)) →
  r14 A C B) ∧
  (∀ (A B C D E F G H I J K L M N : Int),
  (r14 H D B) →
  (r24 E D C B) →
  (r12 A C B) →
  (r1 M L C B) →
  (r9 I E C B) →
  (¬((0 : Int) = K) = (E = (0 : Int))) →
  (¬((0 : Int) = J) = (H = I)) →
  (((0 : Int) = G) = (B ≤ D)) →
  (¬(0 : Int) = F) →
  ((0 : Int) = K) →
  ((0 : Int) = J) →
  (¬(0 : Int) = G) →
  (N = (1 : Int) + M) →
  (L = (-1 : Int) + E) →
  (((0 : Int) = F) = (C ≤ E)) →
  r12 A C B))) ∧
  (((∀ (A B C D E F G H I J K L : Int),
  (r14 J D B) →
  (r24 E D C B) →
  (r12 A C B) →
  (r9 K E C B) →
  (((0 : Int) = I) = (B ≤ D)) →
  (((0 : Int) = H) = (C ≤ E)) →
  (¬(0 : Int) = L) →
  (¬(0 : Int) = I) →
  (¬(0 : Int) = H) →
  (G = (1 : Int) + E) →
  (F = (1 : Int) + D) →
  (¬((0 : Int) = L) = (J = K)) →
  r12 A C B) ∧
  (∀ (A B C D E F G H I J K L : Int),
  (r14 I D B) →
  (r24 E D C B) →
  (r12 A C B) →
  (r9 J E C B) →
  (¬((0 : Int) = K) = (I = J)) →
  (((0 : Int) = H) = (B ≤ D)) →
  (((0 : Int) = G) = (C ≤ E)) →
  (¬(0 : Int) = L) →
  ((0 : Int) = K) →
  (¬(0 : Int) = H) →
  (¬(0 : Int) = G) →
  (F = (1 : Int) + D) →
  (¬((0 : Int) = L) = (E = (0 : Int))) →
  r12 A C B)) ∧
  ((∀ (A B C D E F G : Int),
  (r14 G C A) →
  (r24 D C B A) →
  (((0 : Int) = E) = (B ≤ D)) →
  (¬(0 : Int) = F) →
  (¬(0 : Int) = E) →
  (((0 : Int) = F) = (A ≤ C)) →
  r12 D B A) ∧
  (∀ (A B C D E F G H I J K L M N O : Int),
  (r14 I E B) →
  (r24 F E C B) →
  (r12 D C B) →
  (r1 N M C B) →
  (r9 J F C B) →
  (r9 A D C B) →
  (¬((0 : Int) = L) = (F = (0 : Int))) →
  (¬((0 : Int) = K) = (I = J)) →
  (((0 : Int) = H) = (B ≤ E)) →
  (¬(0 : Int) = G) →
  ((0 : Int) = L) →
  ((0 : Int) = K) →
  (¬(0 : Int) = H) →
  (O = (1 : Int) + N) →
  (M = (-1 : Int) + F) →
  (((0 : Int) = G) = (C ≤ F)) →
  r9 A D C B)))) ∧
  ((((∀ (A B C D E F G H I J K L M : Int),
  (r14 K E B) →
  (r24 F E C B) →
  (r12 D C B) →
  (r9 L F C B) →
  (r9 A D C B) →
  (((0 : Int) = J) = (B ≤ E)) →
  (((0 : Int) = I) = (C ≤ F)) →
  (¬(0 : Int) = M) →
  (¬(0 : Int) = J) →
  (¬(0 : Int) = I) →
  (H = (1 : Int) + F) →
  (G = (1 : Int) + E) →
  (¬((0 : Int) = M) = (K = L)) →
  r9 A D C B) ∧
  (∀ (A B C D E F G H I J K L M : Int),
  (r14 J E B) →
  (r24 F E C B) →
  (r12 D C B) →
  (r9 K F C B) →
  (r9 A D C B) →
  (¬((0 : Int) = L) = (J = K)) →
  (((0 : Int) = I) = (B ≤ E)) →
  (((0 : Int) = H) = (C ≤ F)) →
  (¬(0 : Int) = M) →
  ((0 : Int) = L) →
  (¬(0 : Int) = I) →
  (¬(0 : Int) = H) →
  (G = (1 : Int) + E) →
  (¬((0 : Int) = M) = (F = (0 : Int))) →
  r9 A D C B)) ∧
  ((∀ (A B C D E F G H I : Int),
  (r12 D C B) →
  (r25 A D C B) →
  (r0 C B) →
  (H = (1 : Int)) →
  (G = (-1 : Int)) →
  (F = (0 : Int)) →
  (E = (0 : Int)) →
  (I = (-1 : Int)) →
  r9 A D C B) ∧
  (∀ (A B C D E F G H I J K L M N : Int),
  (r14 H D B) →
  (r24 E D C B) →
  (r9 I E C B) →
  (r1 M L C B) →
  (r21 A C B) →
  (¬((0 : Int) = K) = (E = (0 : Int))) →
  (¬((0 : Int) = J) = (H = I)) →
  (((0 : Int) = G) = (B ≤ D)) →
  (¬(0 : Int) = F) →
  ((0 : Int) = K) →
  ((0 : Int) = J) →
  (¬(0 : Int) = G) →
  (N = (1 : Int) + M) →
  (L = (-1 : Int) + E) →
  (((0 : Int) = F) = (C ≤ E)) →
  r21 A C B))) ∧
  (((∀ (A B C D E F G H I J K L : Int),
  (r14 J D B) →
  (r24 E D C B) →
  (r9 K E C B) →
  (r21 A C B) →
  (((0 : Int) = I) = (B ≤ D)) →
  (((0 : Int) = H) = (C ≤ E)) →
  (¬(0 : Int) = L) →
  (¬(0 : Int) = I) →
  (¬(0 : Int) = H) →
  (G = (1 : Int) + E) →
  (F = (1 : Int) + D) →
  (¬((0 : Int) = L) = (J = K)) →
  r21 A C B) ∧
  (∀ (A B C D E F G H I J K L : Int),
  (r14 I D B) →
  (r24 E D C B) →
  (r9 J E C B) →
  (r21 A C B) →
  (¬((0 : Int) = K) = (I = J)) →
  (((0 : Int) = H) = (B ≤ D)) →
  (((0 : Int) = G) = (C ≤ E)) →
  (¬(0 : Int) = L) →
  ((0 : Int) = K) →
  (¬(0 : Int) = H) →
  (¬(0 : Int) = G) →
  (F = (1 : Int) + D) →
  (¬((0 : Int) = L) = (E = (0 : Int))) →
  r21 A C B)) ∧
  ((∀ (A B C D E F G H I J K : Int),
  (r14 G C A) →
  (r24 D C B A) →
  (r9 H D B A) →
  (¬((0 : Int) = I) = (G = H)) →
  (((0 : Int) = F) = (A ≤ C)) →
  (((0 : Int) = E) = (B ≤ D)) →
  ((0 : Int) = J) →
  ((0 : Int) = I) →
  (¬(0 : Int) = F) →
  (¬(0 : Int) = E) →
  (K = (-1 : Int) + D) →
  (¬((0 : Int) = J) = (D = (0 : Int))) →
  r21 K B A) ∧
  (∀ (A B C D E F G H I J K L M : Int),
  (r14 G C A) →
  (r24 D C B A) →
  (r9 H D B A) →
  (r1 L K B A) →
  (¬((0 : Int) = J) = (D = (0 : Int))) →
  (¬((0 : Int) = I) = (G = H)) →
  (((0 : Int) = F) = (A ≤ C)) →
  (¬(0 : Int) = E) →
  ((0 : Int) = J) →
  ((0 : Int) = I) →
  (¬(0 : Int) = F) →
  (M = (1 : Int) + L) →
  (K = (-1 : Int) + D) →
  (((0 : Int) = E) = (B ≤ D)) →
  r24 M C B A))))) ∧
  (((((∀ (A B C D E F G H I J K : Int),
  (r14 I C A) →
  (r24 D C B A) →
  (r9 J D B A) →
  (((0 : Int) = H) = (A ≤ C)) →
  (((0 : Int) = G) = (B ≤ D)) →
  (¬(0 : Int) = K) →
  (¬(0 : Int) = H) →
  (¬(0 : Int) = G) →
  (F = (1 : Int) + D) →
  (E = (1 : Int) + C) →
  (¬((0 : Int) = K) = (I = J)) →
  r24 F E B A) ∧
  (∀ (A B C D E F G H I J K : Int),
  (r14 H C A) →
  (r24 D C B A) →
  (r9 I D B A) →
  (¬((0 : Int) = J) = (H = I)) →
  (((0 : Int) = G) = (A ≤ C)) →
  (((0 : Int) = F) = (B ≤ D)) →
  (¬(0 : Int) = K) →
  ((0 : Int) = J) →
  (¬(0 : Int) = G) →
  (¬(0 : Int) = F) →
  (E = (1 : Int) + C) →
  (¬((0 : Int) = K) = (D = (0 : Int))) →
  r24 D E B A)) ∧
  ((∀ (A B C D E F G : Int),
  (r0 B A) →
  (F = (1 : Int)) →
  (E = (-1 : Int)) →
  (D = (0 : Int)) →
  (C = (0 : Int)) →
  (G = (-1 : Int)) →
  r24 D C B A) ∧
  (∀ (A B C D E F G H : Int),
  let a!1 := ((0 : Int) = G) = (¬(0 : Int) = E ∧ ¬(0 : Int) = F);
  r7 H B →
    r10 A H C B →
      ((0 : Int) = F) = (D ≤ (0 : Int)) → ((0 : Int) = E) = (B ≤ (0 : Int)) → ¬(0 : Int) = G → ¬a!1 → r23 A H B))) ∧
  (((∀ (A B C D E F G H : Int),
  let a!1 := ((0 : Int) = G) = (¬(0 : Int) = E ∧ ¬(0 : Int) = F);
  r20 H C B →
    r10 A H D C →
      ((0 : Int) = F) = (C ≤ (0 : Int)) → ((0 : Int) = E) = (B ≤ (0 : Int)) → ¬(0 : Int) = G → ¬a!1 → r25 A H C B) ∧
  (∀ (A B C D E F G H : Int),
  let a!1 := ((0 : Int) = H) = (¬(0 : Int) = F ∧ ¬(0 : Int) = G);
  r5 D C B →
    ((0 : Int) = G) = (B ≤ D) →
      ¬((0 : Int) = F) = ((0 : Int) ≤ D) → ¬(0 : Int) = H → E = (1 : Int) → A = C → ¬a!1 → r10 A D C B)) ∧
  ((∀ (A B C D E v_5 : Int),
  (r2 E B C v_5) →
  (r18 A D C B) →
  (r11 D C B) →
  (v_5 = B) →
  r17 A E D C B) ∧
  (∀ (A B C D E : Int),
  let a!1 := ((0 : Int) = E) = (¬(0 : Int) = C ∧ ¬(0 : Int) = D);
  ((0 : Int) = D) = (B ≤ (0 : Int)) → ((0 : Int) = C) = (A ≤ (0 : Int)) → ¬(0 : Int) = E → ¬a!1 → r0 B A)))) ∧
  (∀ (A B C D E F : Int),
  let a!1 := ((0 : Int) = F) = (¬(0 : Int) = D ∧ ¬(0 : Int) = E);
  r5 C B A → ((0 : Int) = E) = (A ≤ C) → ¬((0 : Int) = D) = ((0 : Int) ≤ C) → (0 : Int) = F → ¬a!1 → False)))

end

theorem problem : Problem := by
  zap
  refine ⟨
    -- r27
    (fun x0 x1 x2 x3 : Int => (0 ≤ x1) ∧ (1 ≤ x3) ∧ (x1 < x2)),
    -- r14
    (fun x0 x1 x2 : Int => (0 ≤ x1) ∧ (x1 < x2)),
    -- r15
    (fun x0 x1 x2 x3 : Int => (1 ≤ x0) ∧ (-1 ≤ x1) ∧ (1 ≤ x3) ∧ (x0 ≤ x2) ∧ (x1 < x0)),
    -- r9
    (fun x0 x1 x2 x3 : Int => (0 ≤ x1) ∧ (x1 < x2) ∧ (x1 < x3)),
    -- r29
    (fun x0 x1 x2 x3 x4 x5 : Int =>
      (-1 ≤ x0) ∧ (1 ≤ x2) ∧ (-1 ≤ x3) ∧ (1 ≤ x5) ∧ (x0 < x1) ∧ (x0 < x2) ∧ (x1 < x4) ∧ (x2 ≤ x4) ∧
        (x3 < x2)),
    -- r8
    (fun x0 x1 x2 : Int => (0 ≤ x0) ∧ (1 ≤ x2) ∧ (x0 < x1)),
    -- r1
    (fun x0 x1 x2 x3 : Int => (-1 ≤ x0) ∧ (x0 < x1) ∧ (x1 < x2) ∧ (x1 < x3)),
    -- r24
    (fun x0 x1 x2 x3 : Int => (0 ≤ x0) ∧ (1 ≤ x2) ∧ (1 ≤ x3) ∧ (x0 ≤ x1) ∧ (x0 ≤ x2) ∧ (x1 ≤ x3)),
    -- r12
    (fun x0 x1 x2 : Int => (0 ≤ x0) ∧ (x0 < x1) ∧ (x0 < x2)),
    -- r21
    (fun x0 x1 x2 : Int => (0 ≤ x0) ∧ (x0 < x1) ∧ (x0 < x2)),
    -- r4
    (fun x0 x1 x2 x3 x4 : Int =>
      (0 ≤ x0) ∧ (1 ≤ x1) ∧ (-1 ≤ x2) ∧ (x0 < x3) ∧ (x0 < x4) ∧ (x1 ≤ x3) ∧ (x2 < x1)),
    -- r16
    (fun x0 x1 x2 x3 x4 x5 : Int =>
      (-1 ≤ x0) ∧ (1 ≤ x2) ∧ (-1 ≤ x3) ∧ (x0 < x1) ∧ (x1 < x4) ∧ (x1 < x5) ∧ (x2 ≤ x4) ∧ (x3 < x2)),
    -- r28
    (fun x0 x1 : Int => (0 ≤ x0) ∧ (x0 < x1)),
    -- r6
    (fun x0 x1 x2 x3 x4 : Int =>
      (0 ≤ x0) ∧ (1 ≤ x1) ∧ (-1 ≤ x2) ∧ (1 ≤ x4) ∧ (x0 < x3) ∧ (x1 ≤ x3) ∧ (x2 < x1)),
    -- r19
    (fun x0 x1 x2 : Int => (0 ≤ x0) ∧ (1 ≤ x2) ∧ (x0 < x1) ∧ (x2 < x1)),
    ?_⟩
  -- Remove equality-bound witnesses from Zap's guards.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goal ← Flex.CHC.compactGoal goal []
    Lean.Elab.Tactic.setGoals [goal]
  
  repeat' apply And.intro
  all_goals grind

#print axioms problem

end MochiKmp

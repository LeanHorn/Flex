import Flex

open Classical

-- Inlined definitions (standalone, no imports needed)
abbrev Arr (t0 : Type) [Inhabited t0] : Type := Int -> t0

@[ext]
structure VectorsAVec (t0 : Type) [Inhabited t0] where
  mkVectorsAVec₀ ::
    elems : (Arr t0)
    len : Int

@[simp, reducible]
def sort_is_sorted_between (a: Arr Int) (lo hi: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi) -> (a i <= a j)

@[simp]
noncomputable def sort_is_bigger (arr: Arr Int) (lo hi p: Int) : Prop :=
  forall ix, (lo <= ix /\ ix < hi) -> (arr ix <= arr p)

@[simp]
noncomputable def sort_is_smaller (arr: Arr Int) (lo hi p: Int) : Prop :=
  forall ix, (lo <= ix /\ ix < hi) -> (arr p <= arr ix)

@[simp]
noncomputable def sort_is_partitioned_by (arr: Arr Int) (lo mid hi pivot: Int) : Prop :=
  sort_is_bigger arr lo mid pivot /\ sort_is_smaller arr mid hi pivot

@[simp]
noncomputable def is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, (lo <= i && i <= hi) -> (∃ j, lo <= j /\ j <= hi /\ new i = old j))

@[simp]
noncomputable def is_frame (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, i < lo -> new i = old i) /\ (∀ i, (hi < i) -> new i = old i)

@[simp]
noncomputable def sort_is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  is_perm old new lo hi /\ is_frame old new lo hi

def SortQuicksortRange := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : (VectorsAVec Int)) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (VectorsAVec Int)) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : (Arr Int)) -> (a14 : Int) -> (a15 : (Arr Int)) -> (a16 : Int) -> Prop,
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     (hi₀ < (VectorsAVec.len old₀)) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         ((¬(lo₀ < hi₀)) ->
          (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
          ((sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (hi₀ + 1))) ∧
          ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems old₀) lo₀ hi₀))
          ) ∧
         ((lo₀ < hi₀) ->
          ∀ (p₀ : Int),
           ∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_partitioned_by (VectorsAVec.elems v₀) lo₀ p₀ (hi₀ + 1) p₀) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) lo₀ hi₀) ∧ (lo₀ ≤ p₀) ∧ (p₀ ≤ hi₀)) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              (p₀ ≥ 0) ->
               ((¬(lo₀ < p₀)) ->
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
               ((lo₀ < p₀) ->
                (((p₀ - 1) ≥ 0)) ∧
                ((lo₀ < (VectorsAVec.len v₀))) ∧
                (((p₀ - 1) < (VectorsAVec.len v₀))) ∧
                (∀ (v₁ : (VectorsAVec Int)),
                 (((VectorsAVec.len v₁) = (VectorsAVec.len v₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₁) lo₀ ((p₀ - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₀) (VectorsAVec.elems v₁) lo₀ (p₀ - 1))) ->
                  ((VectorsAVec.len v₁) ≥ 0) ->
                   ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₁) (VectorsAVec.len v₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))))
                ) ∧
               (∀ (a'₃ : (VectorsAVec Int)),
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                 ((¬(p₀ < hi₀)) ->
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                 ((p₀ < hi₀) ->
                  (((p₀ + 1) < (VectorsAVec.len a'₃))) ∧
                  ((hi₀ < (VectorsAVec.len a'₃))) ∧
                  (∀ (v₂ : (VectorsAVec Int)),
                   (((VectorsAVec.len v₂) = (VectorsAVec.len a'₃)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₂) (p₀ + 1) (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems a'₃) (VectorsAVec.elems v₂) (p₀ + 1) hi₀)) ->
                    ((VectorsAVec.len v₂) ≥ 0) ->
                     ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems v₂) (VectorsAVec.len v₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                  ) ∧
                 (∀ (a'₅ : (VectorsAVec Int)),
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₅) (VectorsAVec.len a'₅) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                   (((VectorsAVec.len a'₅) = (VectorsAVec.len old₀))) ∧
                   ((sort_is_sorted_between (VectorsAVec.elems a'₅) lo₀ (hi₀ + 1))) ∧
                   ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems a'₅) lo₀ hi₀))
                   )
                 )
               )

theorem bigger_perm :
  sort_is_bigger a lo p p -> sort_is_perm a a' lo (p-1) -> sort_is_bigger a' lo p p
  := by
  intros; simp_all [sort_is_bigger, sort_is_perm, is_perm, is_frame]; grind

theorem sort_is_perm_trans :
  sort_is_perm old new lo hi -> sort_is_perm new new' lo hi -> sort_is_perm old new' lo hi
  := by
  intros; simp_all [sort_is_perm, is_perm, is_frame]; grind

theorem sort_is_perm_id : sort_is_perm arr arr lo hi := by
  intros; simp_all [sort_is_perm, is_perm, is_frame]; intros i _ _; exists i

theorem is_perm_trans :
  is_perm old new lo hi -> is_perm new new' lo hi -> is_perm old new' lo hi
  := by
  intros; simp_all [is_perm]; grind

theorem is_perm_id : is_perm arr arr lo hi := by
  intros; simp_all [is_perm]; intros i _ _; exists i

theorem is_smaller_perm' :
  sort_is_smaller a p hi p -> sort_is_perm a a' lo (p - 1) -> sort_is_smaller a' p hi p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_smaller_perm :
  sort_is_smaller a1 p (hi + 1) p -> sort_is_perm a1 a2 (p + 1) hi -> sort_is_smaller a2 p (hi + 1) p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem perm_widen_lo :
  sort_is_perm v a lo (p - 1) -> p ≤ hi -> sort_is_perm v a lo hi
  := by
  intro h hp; simp_all [sort_is_perm, is_perm, is_frame]; grind

theorem perm_widen_hi :
  sort_is_perm a b (p + 1) hi -> lo ≤ p -> sort_is_perm a b lo hi
  := by
  intro h hp; simp_all [sort_is_perm, is_perm, is_frame]; grind

theorem is_sorted_using_pivot :
  sort_is_sorted_between a lo p ->
  sort_is_sorted_between a (p + 1) (hi + 1) ->
  sort_is_bigger a lo p p ->
  sort_is_smaller a p (hi + 1) p ->
  sort_is_sorted_between a lo (hi + 1)
  := by
  simp_all [sort_is_smaller, sort_is_bigger, sort_is_sorted_between]; grind

set_option maxHeartbeats 1600000 in
theorem SortQuicksortRange_proof : SortQuicksortRange := by
  unfold SortQuicksortRange
  zap
  solve_fixpoint

theorem SortQuicksortRange_proof' : SortQuicksortRange := by
  unfold SortQuicksortRange
  zap
  intro old₀ lo₀ hi₀ hlolen hhilen hlen hlo hhi
  refine ⟨?_, ?_⟩
  · -- base case: ¬ lo₀ < hi₀
    intro hnlt
    refine ⟨rfl, ?_, ?_⟩
    · simp [sort_is_sorted_between]; grind
    · apply sort_is_perm_id
  · -- recursive case: lo₀ < hi₀
    intro hlt p₀ v₀ hv₀ hv₀len hp₀
    obtain ⟨hv₀_len, hpart, hperm₀, hlop, hphi⟩ := hv₀
    refine ⟨?_, ?_⟩
    · intro hlolt; refine ⟨by omega, by omega, by omega⟩
    · intro a'₃ hbranch
      -- hbranch : (¬lo₀ < p₀ ∧ …) ∨ (lo₀ < p₀ ∧ ∃ v₁, …) — the lower-half recursive call result
      -- facts about a'₃ (result of sorting the lower half [lo₀, p₀))
      have ha3len : a'₃.len = old₀.len := by
        rcases hbranch with ⟨_, h⟩ | ⟨_, _, h⟩ <;> grind
      have ha3sorted : sort_is_sorted_between a'₃.elems lo₀ p₀ := by
        rcases hbranch with ⟨hn, h⟩ | ⟨_, vv, h⟩ <;> grind
      have ha3p : a'₃.elems p₀ = v₀.elems p₀ := by
        rcases hbranch with ⟨_, h⟩ | ⟨_, vv, ⟨_, _, hpm⟩, _, h⟩ <;>
          (try simp only [sort_is_perm, is_frame] at hpm) <;> grind
      have ha3perm : sort_is_perm v₀.elems a'₃.elems lo₀ (p₀ - 1) := by
        rcases hbranch with ⟨_, h⟩ | ⟨_, vv, ⟨_, _, hpm⟩, _, h⟩ <;>
          simp only [sort_is_perm, is_perm, is_frame] at * <;> grind
      have ha3bigger : sort_is_bigger a'₃.elems lo₀ p₀ p₀ := bigger_perm hpart.1 ha3perm
      have ha3smaller : sort_is_smaller a'₃.elems p₀ (hi₀ + 1) p₀ := is_smaller_perm' hpart.2 ha3perm
      refine ⟨?_, ?_⟩
      · intro hph; exact ⟨by omega, by omega⟩
      · intro a'₅ hbr5
        -- hbr5 : (¬p₀ < hi₀ ∧ …) ∨ (p₀ < hi₀ ∧ ∃ v₂, …) — the upper-half recursive call result
        -- facts about a'₅ (result of sorting the upper half (p₀, hi₀])
        have ha5len : a'₅.len = old₀.len := by
          rcases hbr5 with ⟨_, h⟩ | ⟨_, vv, h⟩ <;> grind
        have ha5sorted_hi : sort_is_sorted_between a'₅.elems (p₀ + 1) (hi₀ + 1) := by
          rcases hbr5 with ⟨hn, h⟩ | ⟨_, vv, h⟩ <;> grind
        have ha5perm : sort_is_perm a'₃.elems a'₅.elems (p₀ + 1) hi₀ := by
          rcases hbr5 with ⟨_, h⟩ | ⟨_, vv, ⟨_, _, hpm⟩, _, h⟩ <;>
            (try simp only [sort_is_perm, is_perm, is_frame] at hpm) <;>
            simp only [sort_is_perm, is_perm, is_frame] <;> grind
        -- a'₅ agrees with a'₃ on the lower half (frame of the upper-half sort)
        have hframe5 : ∀ i, i < p₀ + 1 → a'₅.elems i = a'₃.elems i := by
          have h := ha5perm; simp only [sort_is_perm, is_frame] at h; exact h.2.1
        have h11 : sort_is_smaller a'₅.elems p₀ (hi₀ + 1) p₀ := is_smaller_perm ha3smaller ha5perm
        have h_lo_p : sort_is_sorted_between a'₅.elems lo₀ p₀ := by
          intro i j hij
          rw [hframe5 i (by omega), hframe5 j (by omega)]; exact ha3sorted i j hij
        have h_p_bigger : sort_is_bigger a'₅.elems lo₀ p₀ p₀ := by
          intro ix hix
          rw [hframe5 ix (by omega), hframe5 p₀ (by omega)]; exact ha3bigger ix hix
        refine ⟨ha5len, is_sorted_using_pivot h_lo_p ha5sorted_hi h_p_bigger h11, ?_⟩
        exact sort_is_perm_trans hperm₀
          (sort_is_perm_trans (perm_widen_lo ha3perm hphi) (perm_widen_hi ha5perm hlop))

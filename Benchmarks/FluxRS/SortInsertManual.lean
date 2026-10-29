import Benchmarks.FluxRS.SortInsert

namespace F

private def insertionInvariant (k : Int) (arr : Arr Int) (len : Int)
    (_old : Arr Int) (oldLen n : Int) : Prop :=
  0 ≤ k ∧ k ≤ n ∧ n < len ∧ len = oldLen ∧
    sort_is_sorted_between_exc arr 0 (n + 1) k

private def insertionResult (_old : Arr Int) (oldLen n _k : Int)
    (arr : Arr Int) (len : Int) : Prop :=
  len = oldLen ∧ sort_is_sorted_between arr 0 (n + 1)

private theorem swap_preserves (arr : Arr Int) (n k : Int)
    (hs : sort_is_sorted_between_exc arr 0 (n + 1) k)
    (hk : 0 < k) (hlt : arr k < arr (k - 1)) :
    sort_is_sorted_between_exc
      (fun i => if i = k then arr (k - 1) else if i = k - 1 then arr k else arr i)
      0 (n + 1) (k - 1) := by
  simp only [sort_is_sorted_between_exc, bne_iff_ne, and_imp] at hs ⊢
  intro i j hi hij hjn hjk1
  by_cases hjk : j = k
  · by_cases hik1 : i = k - 1
    · grind
    · have h := hs i (k - 1) (by omega) (by omega) (by omega) (by omega)
      grind
  · by_cases hik : i = k
    · have h := hs (k - 1) j (by omega) (by omega) (by omega) (by omega)
      grind
    · by_cases hik1 : i = k - 1
      · have h := hs k j (by omega) (by omega) (by omega) (by omega)
        grind
      · have h := hs i j hi hij hjn hjk
        grind

private theorem sorted_at_exit (arr : Arr Int) (n k : Int)
    (hs : sort_is_sorted_between_exc arr 0 (n + 1) k)
    (hk : 0 ≤ k) (stop : k ≤ 0 ∨ (0 < k ∧ arr (k - 1) ≤ arr k)) :
    sort_is_sorted_between arr 0 (n + 1) := by
  simp only [sort_is_sorted_between_exc, sort_is_sorted_between,
    bne_iff_ne, and_imp] at hs ⊢
  intro i j hi hij hjn
  rcases stop with hk0 | ⟨hk0, hord⟩
  · exact hs i j hi hij hjn (by omega)
  · by_cases hjk : j = k
    · by_cases hik1 : i = k - 1
      · grind
      · have h := hs i (k - 1) (by omega) (by omega) (by omega) (by omega)
        grind
    · exact hs i j hi hij hjn hjk

theorem SortInsert_manual : SortInsert := by
  refine ⟨insertionInvariant, insertionResult,
    (fun _ _ _ _ _ _ _ => True), (fun _ _ _ _ _ _ _ => True), ?_⟩
  intro old n hs hn _ hn0
  constructor
  · exact ⟨hn0, Int.le_refl n, hn.2, rfl, hs⟩
  · intro k arr hinv
    rcases hinv with ⟨hk0, hkn, hnlen, hlen, hs⟩
    constructor
    · intro hstop
      exact ⟨hlen, sorted_at_exit arr.elems n k hs hk0 (.inl (by omega))⟩
    constructor
    · intro hk
      refine ⟨by omega, (fun _ => True.intro), ?_⟩
      intro _
      refine ⟨by omega, by omega, (fun _ => True.intro), ?_⟩
      intro _
      constructor
      · intro hstop
        have hord : arr.elems (k - 1) ≤ arr.elems k := by
          simpa only [vectors_arr_get, LeanProofs.Lib.Lemmas.arr_get] using
            Int.le_of_not_gt hstop
        exact ⟨hlen, sorted_at_exit arr.elems n k hs hk0 (.inr ⟨hk, hord⟩)⟩
      · intro hswap
        refine ⟨by omega, by omega, by omega, ?_⟩
        intro _
        refine ⟨by omega, ?_⟩
        refine ⟨by omega, by omega, hnlen, hlen, ?_⟩
        change sort_is_sorted_between_exc
          (fun i => if i = k then arr.elems (k - 1)
            else if i = k - 1 then arr.elems k else arr.elems i) 0 (n + 1) (k - 1)
        exact swap_preserves arr.elems n k hs hk hswap
    · exact fun hresult => hresult

end F

#print axioms F.SortInsert_manual

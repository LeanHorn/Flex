import Flex.VCG.STLC.Soundness

/-! # Measures: the facts constructors and matches reveal are true

  A measure is uninterpreted in verification conditions, but the semantic
  model fixes it to the structurally recursive function its declaration
  defines (`DEnv.measEval`). The facts the typing rules record — at a
  constructor application (`DEnv.ctorRefine`) and in a match alternative
  (`DEnv.caseFacts`, at the payload's last field) — are then true by
  unfolding that definition once, on whatever values the fields hold: no typing
  or step-index argument is involved. -/

namespace STLC

/-! ## Looking up measure bodies -/

theorem List.lookup_of_mem_nodup' {β : Type} :
    ∀ {l : List (String × β)} {a : String} {b : β}, (l.map Prod.fst).Nodup → (a, b) ∈ l →
      l.lookup a = some b
  | [], _, _, _, h => by simp at h
  | (a', b') :: tl, a, b, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [List.lookup]
    · have hmem : a ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(a, b), h, rfl⟩
      have hne : a ≠ a' := fun he => hnd.1 (he ▸ hmem)
      have : (a == a') = false := by simp [hne]
      simp only [List.lookup, this]
      exact List.lookup_of_mem_nodup' hnd.2 h

theorem DataDecl.measBody?_of_mem {d : DataDecl} {j : Nat} {mb : String × MBody}
    (hnd : (d.measures.map Prod.fst).Nodup) (h : mb ∈ d.ctorMeasures j) :
    d.measBody? mb.1 j = some mb.2 := by
  simp only [DataDecl.ctorMeasures, List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, b, hb, rfl⟩ := h
  have hl : d.measures.lookup x.1 = some x.2 := List.lookup_of_mem_nodup' hnd (by simpa using hx)
  simp only [DataDecl.measBody?, hl, Option.bind_some, hb]

/-- What `DEnv.wfB` guarantees about the measures of a declaration. -/
theorem DEnv.wfB_meas {de : DEnv} (h : de.wfB = true) {C : String} {d : DataDecl}
    (hd : de.decl? C = some d) :
    (d.measures.map Prod.fst).Nodup ∧
      ∀ j mb c, mb ∈ d.ctorMeasures j → d.ctorFields[j]? = some c → mb.2.idxOK c.2.length = true := by
  have hmem := List.mem_of_lookup_eq_some' hd
  simp only [DEnv.wfB, Bool.and_eq_true, List.all_eq_true] at h
  have hok := h.2 (C, d) hmem
  simp only [DataDecl.measOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  refine ⟨hok.1, fun j mb c hmb hc => ?_⟩
  simp only [DataDecl.ctorMeasures, List.mem_filterMap, Option.map_eq_some_iff] at hmb
  obtain ⟨x, hx, b, hb, rfl⟩ := hmb
  have hzip : (b, c) ∈ x.2.zip d.ctorFields := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, by simp [List.getElem?_zip_eq_some, hb, hc]⟩
  exact hok.2 x hx (b, c) hzip

/-! ## Evaluating facts -/

theorem Formula.interp_conjAll (γ : REnv) : ∀ (φs : List Formula),
    Formula.interp γ (Formula.conjAll φs) ↔ ∀ φ ∈ φs, Formula.interp γ φ
  | [] => by simp [Formula.conjAll, Formula.interp]
  | φ :: φs => by simp [Formula.conjAll, Formula.interp, Formula.interp_conjAll γ φs]

theorem MBody.interp_toTerm (γ : REnv) (fld : Nat → Term .int) (msr : String → Nat → Term .int) :
    ∀ (b : MBody),
      Term.interp γ (b.toTerm fld msr) =
        b.eval (fun i => Term.interp γ (fld i)) (fun i m => Term.interp γ (msr m i))
  | .const _ => rfl
  | .field _ => rfl
  | .meas _ _ => rfl
  | .add x y => by
    simp only [MBody.toTerm, MBody.eval, Term.interp, MBody.interp_toTerm γ fld msr x,
      MBody.interp_toTerm γ fld msr y]
  | .iteLe x y t e => by
    simp only [MBody.toTerm, MBody.eval, Term.interp, MBody.interp_toTerm γ fld msr x,
      MBody.interp_toTerm γ fld msr y, MBody.interp_toTerm γ fld msr t,
      MBody.interp_toTerm γ fld msr e, decide_eq_true_eq]

theorem MBody.eval_congr {n : Nat} {fv gv : Nat → Int} {f g : Nat → String → Int}
    (hv : ∀ i < n, fv i = gv i) (hfg : ∀ i < n, ∀ m, f i m = g i m) :
    ∀ (b : MBody), b.idxOK n = true → b.eval fv f = b.eval gv g
  | .const _, _ => rfl
  | .field i, h => by
    simp only [MBody.idxOK, decide_eq_true_eq] at h
    exact hv i h
  | .meas m i, h => by
    simp only [MBody.idxOK, decide_eq_true_eq] at h
    exact hfg i h m
  | .add x y, h => by
    simp only [MBody.idxOK, Bool.and_eq_true] at h
    simp only [MBody.eval, MBody.eval_congr hv hfg x h.1, MBody.eval_congr hv hfg y h.2]
  | .iteLe x y t e, h => by
    simp only [MBody.idxOK, Bool.and_eq_true] at h
    simp only [MBody.eval, MBody.eval_congr hv hfg x h.1.1.1, MBody.eval_congr hv hfg y h.1.1.2,
      MBody.eval_congr hv hfg t h.1.2, MBody.eval_congr hv hfg e h.2]

/-! ## Payloads -/

/-- A payload with the fields `vs`: a unit, the field, or nested pairs. -/
def Val.ofList : List Val → Val
  | []      => .iconst 0
  | [v]     => v
  | v :: vs => .pair v (Val.ofList vs)

theorem Val.fieldsN_ofList : ∀ vs, (Val.ofList vs).fieldsN vs.length = vs
  | [] => rfl
  | [v] => rfl
  | v :: v' :: vs => by
    have := Val.fieldsN_ofList (v' :: vs)
    simp only [List.length_cons] at this ⊢
    simp only [Val.ofList, Val.fieldsN, this]

/-- Push the values `vs` onto the de Bruijn stack, in order. -/
def REnv.pushAll (γ : REnv) : List Val → REnv
  | []      => γ
  | v :: vs => (γ.push v).pushAll vs

theorem REnv.pushAll_bv : ∀ (γ : REnv) (vs : List Val), (γ.pushAll vs).bv = vs.reverse ++ γ.bv
  | _, [] => rfl
  | γ, v :: vs => by simp [REnv.pushAll, REnv.pushAll_bv _ vs]

theorem REnv.pushAll_map : ∀ (γ : REnv) (vs : List Val), (γ.pushAll vs).map = γ.map
  | _, [] => rfl
  | γ, v :: vs => by simp [REnv.pushAll, REnv.pushAll_map _ vs]

theorem REnv.pushAll_sorts : ∀ (γ : REnv) (vs : List Val), (γ.pushAll vs).sorts = γ.sorts
  | _, [] => rfl
  | γ, v :: vs => by simp [REnv.pushAll, REnv.pushAll_sorts _ vs]

/-- With the fields `vs` pushed, field `i` is the de Bruijn slot `vs.length - 1 - i`. -/
theorem REnv.pushAll_field (γ : REnv) (vs : List Val) (i : Nat) (hi : i < vs.length) :
    (γ.pushAll vs).bv[vs.length - 1 - i]? = some vs[i] := by
  rw [REnv.pushAll_bv, List.getElem?_append_left (by simp; omega),
    List.getElem?_reverse (by omega), show vs.length - 1 - (vs.length - 1 - i) = i by omega,
    List.getElem?_eq_getElem hi]

/-- The fields behind a payload type. -/
theorem DEnv.payload?_fields {de : DEnv} {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) :
    ∃ d c, de.decl? C = some d ∧ d.ctorFields[j]? = some c ∧ P = Ty.tuple c.2 ∧
      de.nFields C j = c.2.length := by
  simp only [DEnv.payload?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hP
  obtain ⟨d, hd, c', hc', rfl⟩ := hP
  simp only [DataDecl.ctors, List.getElem?_map, Option.map_eq_some_iff] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  exact ⟨d, c, hd, hc, rfl, by simp [DEnv.nFields, DEnv.fields?, hd, hc]⟩

/-! ## Strengthening the last field -/

/-- A payload in `t` is in `t` with `r` conjoined into its last component,
    provided `r` holds with the payload's fields pushed. -/
theorem TyDenote.strengthenLast {κ : KEnv} {δ : TyEnvSem} {k : Nat} (r : Refinement) :
    ∀ (n : Nat) (t : Ty) (γ : REnv) (w : Val), TyDenote κ δ k t γ w →
      ((w.fieldsN (n + 1)).length = n + 1 →
        Refinement.interp κ r ((γ.withSorts δ.sorts).pushAll (w.fieldsN (n + 1)))) →
      TyDenote κ δ k (t.strengthenLast n r) γ w
  | 0, .refine b r', γ, w, h, H => by
    simp only [Ty.strengthenLast, TyDenote, Refinement.interp] at h ⊢
    exact ⟨h.1, h.2, H rfl⟩
  | 0, .data C n a r', γ, w, h, H => by
    simp only [Ty.strengthenLast, TyDenote, Refinement.interp] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, h2, h3, ⟨h4, H rfl⟩, h5⟩
  | n + 1, .prod s t, γ, w, h, H => by
    simp only [Ty.strengthenLast, TyDenote] at h ⊢
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    refine ⟨v₁, v₂, rfl, h₁, TyDenote.strengthenLast r n t (γ.push v₁) v₂ h₂ fun hl => ?_⟩
    exact H (by simp [Val.fieldsN, hl])
  | 0, .arrow _ _, _, _, h, _ | 0, .forall _ _, _, _, h, _ | 0, .prod _ _, _, _, h, _ => by
    simpa [Ty.strengthenLast] using h
  | _ + 1, .refine _ _, _, _, h, _ | _ + 1, .arrow _ _, _, _, h, _ | _ + 1, .forall _ _, _, _, h, _
  | _ + 1, .data _ _ _ _, _, _, h, _ => by
    simpa [Ty.strengthenLast] using h

/-! ## The facts are true -/

/-- What a constructor application records about its result holds. -/
theorem DEnv.ctorRefine_sound {κ : KEnv} {de : DEnv} {C : String} {j : Nat} {e : Exp} {γ : REnv}
    {σ : SortEnv} (hσ : σ.meas = de.measEval) {w : Val}
    (hnd : ∀ d, de.decl? C = some d → (d.measures.map Prod.fst).Nodup)
    (hw : ∀ as, e.tupleVarsN (de.nFields C j) = some as →
      w.fieldsN (de.nFields C j) = as.map γ.map) :
    Refinement.interp κ (de.ctorRefine C j e) ((γ.withSorts σ).push (.ctor C j w)) := by
  unfold DEnv.ctorRefine
  split
  · rename_i as has
    have hf := hw as has
    simp only [DEnv.ctorFacts, Refinement.interp, Formula.interp_conjAll, List.mem_map]
    rintro _ ⟨mb, hmb, rfl⟩
    simp only [DEnv.ctorMeasures] at hmb
    cases hd : de.decl? C with
    | none => simp [hd] at hmb
    | some d =>
      simp only [hd, Option.map_some, Option.getD_some] at hmb
      simp only [Formula.interp]
      rw [MBody.interp_toTerm]
      simp only [Term.interp, REnv.push, REnv.withSorts, List.getElem?_cons_zero, Option.getD_some, hσ]
      rw [DEnv.measEval_ctor]
      simp only [hd, Option.bind_some, DataDecl.measBody?_of_mem (hnd d hd) hmb]
      congr 1
      · funext i
        by_cases hi : i < as.length
        · have hi' : i < (w.fieldsN (de.nFields C j)).length := by simp [hf, hi]
          simp [hi, hi', hf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          simp [Term.interp]
        · have hi' : ¬ i < (w.fieldsN (de.nFields C j)).length := by simp [hf, hi]
          simp [hi, hi', Term.interp]
      · funext i m'
        by_cases hi : i < as.length
        · have hi' : i < (w.fieldsN (de.nFields C j)).length := by simp [hf, hi]
          simp [hi, hi', hf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          simp [Term.interp, hσ]
        · have hi' : ¬ i < (w.fieldsN (de.nFields C j)).length := by simp [hf, hi]
          simp [hi, hi', Term.interp]
  · simp [Refinement.interp, Formula.interp]

/-- What matching `x` against `C j` records at the payload's last field holds. -/
theorem DEnv.caseFacts_sound {κ : KEnv} {de : DEnv} {C : String} {j : Nat} {x : EVar}
    {E : REnv} {w : Val}
    (hmeas : E.sorts.meas = de.measEval) (hx : E.map x = .ctor C j w)
    (hbv : ∀ i (hi : i < de.nFields C j), ∃ h : i < (w.fieldsN (de.nFields C j)).length,
      E.bv[de.nFields C j - 1 - i]? = some (w.fieldsN (de.nFields C j))[i])
    (hnd : ∀ d, de.decl? C = some d → (d.measures.map Prod.fst).Nodup)
    (hidx : ∀ mb ∈ de.ctorMeasures C j, mb.2.idxOK (de.nFields C j) = true) :
    Refinement.interp κ (de.caseFacts C j (de.nFields C j) x) E := by
  simp only [DEnv.caseFacts, Refinement.interp, Formula.interp_conjAll, List.mem_map]
  rintro _ ⟨mb, hmb, rfl⟩
  have hidx' := hidx mb hmb
  simp only [DEnv.ctorMeasures] at hmb
  cases hd : de.decl? C with
  | none => simp [hd] at hmb
  | some d =>
    simp only [hd, Option.map_some, Option.getD_some] at hmb
    simp only [Formula.interp]
    rw [MBody.interp_toTerm]
    simp only [Term.interp, hx, hmeas]
    rw [DEnv.measEval_ctor]
    simp only [hd, Option.bind_some, DataDecl.measBody?_of_mem (hnd d hd) hmb]
    apply MBody.eval_congr ?_ ?_ mb.2 hidx'
    · intro i hi
      obtain ⟨h, hb⟩ := hbv i hi
      simp only [dif_pos h, hb, Option.getD_some]
    · intro i hi m'
      obtain ⟨h, hb⟩ := hbv i hi
      simp only [dif_pos h, hb, Option.getD_some]

/-! ## Payloads written out as variables -/

theorem Exp.tupleVarsN_length : ∀ {n : Nat} {e : Exp} {as : List EVar},
    e.tupleVarsN n = some as → as.length = n := by
  intro n e
  induction n, e using Exp.tupleVarsN.induct with
  | case1 => intro as h; simp only [Exp.tupleVarsN, Option.some.injEq] at h; subst h; rfl
  | case2 => intro as h; simp only [Exp.tupleVarsN, Option.some.injEq] at h; subst h; rfl
  | case3 n x e ih =>
    intro as h
    simp only [Exp.tupleVarsN, Option.map_eq_some_iff] at h
    obtain ⟨as', h', rfl⟩ := h
    simp [ih h']
  | case4 => intro as h; simp_all [Exp.tupleVarsN]

theorem Exp.tupleVarsN_fv : ∀ {n : Nat} {e : Exp} {as : List EVar},
    e.tupleVarsN n = some as → ∀ a ∈ as, a ∈ e.fv := by
  intro n e
  induction n, e using Exp.tupleVarsN.induct with
  | case1 => intro as h; simp only [Exp.tupleVarsN, Option.some.injEq] at h; subst h; simp
  | case2 x =>
    intro as h; simp only [Exp.tupleVarsN, Option.some.injEq] at h; subst h; simp [Exp.fv]
  | case3 n x e ih =>
    intro as h a ha
    simp only [Exp.tupleVarsN, Option.map_eq_some_iff] at h
    obtain ⟨as', h', rfl⟩ := h
    simp only [List.mem_cons] at ha
    simp only [Exp.fv, List.mem_append, List.mem_singleton]
    rcases ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (ih h' a ha)
  | case4 => intro as h; simp_all [Exp.tupleVarsN]

/-- Fields given as variables evaluate to a payload holding their values. -/
theorem Exp.tupleVarsN_substEnv (γ : REnv) : ∀ {n : Nat} {e : Exp} {as : List EVar},
    e.tupleVarsN (n + 1) = some as → (∀ a ∈ as, Val.Erased (γ.map a)) →
    (e.substEnv γ).erase = (Val.ofList (as.map γ.map)).toExp := by
  intro n
  induction n with
  | zero =>
    intro e as h her
    cases e <;> simp [Exp.tupleVarsN] at h
    rename_i x
    subst h
    simp only [Exp.substEnv, List.map_cons, List.map_nil, Val.ofList]
    exact Exp.erase_of_typeFree _ (her x (by simp))
  | succ n ih =>
    intro e as h her
    cases e <;> (try simp [Exp.tupleVarsN] at h)
    rename_i e₁ e₂
    cases e₁ <;> (try simp [Exp.tupleVarsN] at h)
    rename_i x
    obtain ⟨as', h', rfl⟩ := h
    have hl := Exp.tupleVarsN_length h'
    obtain ⟨a', as'', rfl⟩ : ∃ a' as'', as' = a' :: as'' := by
      cases as' with
      | nil => simp at hl
      | cons a' as'' => exact ⟨a', as'', rfl⟩
    have ih' := ih h' (fun a ha => her a (List.mem_cons_of_mem _ ha))
    simp only [Exp.substEnv, Exp.erase, ih', List.map_cons, Val.ofList, Val.toExp]
    rw [Exp.erase_of_typeFree _ (her x List.mem_cons_self)]

/-- The payload a constructor applied to variables builds has their values as
    its fields. -/
theorem Exp.tupleVarsN_eval {γ : REnv} {n k m : Nat} {e : Exp} {as : List EVar} {w : Val}
    (h : e.tupleVarsN n = some as) (her : ∀ a ∈ as, Val.Erased (γ.map a))
    (hev : Eval k (e.substEnv γ).erase (.val w m)) : w.fieldsN n = as.map γ.map := by
  cases n with
  | zero =>
    simp only [Exp.tupleVarsN, Option.some.injEq] at h
    subst h; rfl
  | succ n =>
    rw [Exp.tupleVarsN_substEnv γ h her] at hev
    have := Eval.toExp_inv hev
    injection this with hw _
    subst hw
    have hl : (as.map γ.map).length = n + 1 := by simp [Exp.tupleVarsN_length h]
    have := Val.fieldsN_ofList (as.map γ.map)
    rw [hl] at this
    exact this

end STLC

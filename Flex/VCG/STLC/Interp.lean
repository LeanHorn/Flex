import Flex.VCG.STLC.Proofs.Semantics

open STLC

/-! # A definitional interpreter

  `interp g n e` runs `e` with `n` units of fuel, as `Eval n e` does, and
  returns the outcome — or says that evaluation is stuck, which `Eval` can only
  express by having no derivation. It is a function, so it computes: a concrete
  program can be run by `rfl`, `decide` or `#eval`.

  Evaluation under `Eval` always terminates, but not structurally: opening a
  `let` body with a value can make it larger. So the interpreter also takes
  *gas* `g`, a bound on its recursion depth, and reports `outOfGas` when that
  runs out. Gas is a property of the interpreter, not of the program: it is
  unrelated to fuel (an `Eval` timeout is the outcome `.ok .timeout`), and once
  there is enough of it, more changes nothing (`interp_mono`).

  The interpreter agrees with the big-step semantics:
  * `interp_sound` — an outcome it returns is derivable;
  * `interp_complete` — a derivable outcome is returned, given enough gas;
  * `interp_stuck` — when it reports `stuck`, no outcome is derivable.
  Together: `interp_iff`, `(∃ g, interp g n e = .ok o) ↔ Eval n e o`. `runI`
  runs a program's erasure, as `Run` does (`runI_iff`, `runI_stuck`). -/

namespace STLC

/-- The result of running the interpreter. -/
inductive Result where
  /-- Evaluation finished with this outcome (a value, or a timeout). -/
  | ok       : Outcome → Result
  /-- Evaluation is stuck: no `Eval` rule applies. -/
  | stuck    : Result
  /-- The interpreter ran out of gas before deciding. -/
  | outOfGas : Result

/-- Continue with a value and the fuel left; timeouts, stuck states and
    running out of gas propagate (the `_to` rules of `Eval`). -/
@[simp] def Result.bind : Result → (Val → Nat → Result) → Result
  | .ok (.val v m), k => k v m
  | .ok .timeout,   _ => .ok .timeout
  | .stuck,         _ => .stuck
  | .outOfGas,      _ => .outOfGas

/-- The interpreter: `interp g n e` evaluates `e` with fuel `n` and gas `g`. -/
def interp : Nat → Nat → Exp → Result
  | 0, _, _ => .outOfGas
  | g+1, n, e =>
    match e with
    | .bvar _ | .fvar _ | .unreach => .stuck
    | .iconst i => .ok (.val (.iconst i) n)
    | .bconst b => .ok (.val (.bconst b) n)
    | .lam body => .ok (.val (.clos body) n)
    | .fix body => .ok (.val (.fclos body) n)
    | .ann e _ | .tabs _ e | .tapp e _ => interp g n e
    | .letin e₁ e₂ =>
      (interp g n e₁).bind fun v₁ n₁ => interp g n₁ (e₂.openVal 0 v₁)
    | .app e₁ e₂ =>
      (interp g n e₁).bind fun f n₁ =>
      (interp g n₁ e₂).bind fun va n₂ =>
      match f.apply va, n₂ with
      | none,      _    => .stuck
      | some _,    0    => .ok .timeout
      | some body, n₃+1 => interp g n₃ body
    | .add e₁ e₂ =>
      (interp g n e₁).bind fun v₁ n₁ =>
      (interp g n₁ e₂).bind fun v₂ n₂ =>
      match v₁, v₂ with
      | .iconst a, .iconst b => .ok (.val (.iconst (a + b)) n₂)
      | _, _ => .stuck
    | .leq e₁ e₂ =>
      (interp g n e₁).bind fun v₁ n₁ =>
      (interp g n₁ e₂).bind fun v₂ n₂ =>
      match Val.leb? v₁ v₂ with
      | some c => .ok (.val (.bconst c) n₂)
      | none   => .stuck
    | .not e =>
      (interp g n e).bind fun v n₁ =>
      match v with
      | .bconst b => .ok (.val (.bconst (!b)) n₁)
      | _ => .stuck
    | .and e₁ e₂ =>
      (interp g n e₁).bind fun v₁ n₁ =>
      (interp g n₁ e₂).bind fun v₂ n₂ =>
      match v₁, v₂ with
      | .bconst a, .bconst b => .ok (.val (.bconst (a && b)) n₂)
      | _, _ => .stuck
    | .ite e₀ e₁ e₂ =>
      (interp g n e₀).bind fun v n₁ =>
      match v with
      | .bconst true  => interp g n₁ e₁
      | .bconst false => interp g n₁ e₂
      | _ => .stuck
    | .pair e₁ e₂ =>
      (interp g n e₁).bind fun v₁ n₁ =>
      (interp g n₁ e₂).bind fun v₂ n₂ =>
      .ok (.val (.pair v₁ v₂) n₂)
    | .split e₁ e₂ =>
      (interp g n e₁).bind fun v n₁ =>
      match v with
      | .pair v₁ v₂ => interp g n₁ (Exp.openVal 0 v₂ (Exp.openVal 1 v₁ e₂))
      | _ => .stuck
    | .ctor C j _ e =>
      (interp g n e).bind fun w n₁ => .ok (.val (.ctor C j w) n₁)
    | .case e m alts =>
      (interp g n e).bind fun v n₁ =>
      match v with
      | .ctor _ j w =>
        if hj : j < m then
          match n₁ with
          | 0    => .ok .timeout
          | n₂+1 => interp g n₂ (Exp.openVal 0 w (alts ⟨j, hj⟩))
        else .stuck
      | _ => .stuck

/-- Run a program as `Run` does: interpret its erasure. -/
def runI (g n : Nat) (e : Exp) : Result := interp g n e.erase

/-! ## Correctness -/

theorem Result.bind_eq_ok {r : Result} {k : Val → Nat → Result} {o : Outcome} :
    r.bind k = .ok o ↔
      (∃ v m, r = .ok (.val v m) ∧ k v m = .ok o) ∨ (r = .ok .timeout ∧ o = .timeout) := by
  rcases r with (⟨v, m⟩ | _) | _ | _ <;> simp [eq_comm]
  exact ⟨fun h => ⟨v, m, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h₁, h₂⟩, h⟩ => h₁ ▸ h₂ ▸ h⟩

theorem Result.bind_eq_stuck {r : Result} {k : Val → Nat → Result} :
    r.bind k = .stuck ↔ r = .stuck ∨ ∃ v m, r = .ok (.val v m) ∧ k v m = .stuck := by
  rcases r with (⟨v, m⟩ | _) | _ | _ <;> simp
  exact ⟨fun h => ⟨v, m, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h₁, h₂⟩, h⟩ => h₁ ▸ h₂ ▸ h⟩

theorem Result.bind_ne_outOfGas {r : Result} {k : Val → Nat → Result}
    (h : r.bind k ≠ .outOfGas) :
    r ≠ .outOfGas ∧ ∀ v m, r = .ok (.val v m) → k v m ≠ .outOfGas := by
  rcases r with (⟨v, m⟩ | _) | _ | _ <;> simp_all

/-- Running with more gas changes nothing, once the result is decided. -/
theorem interp_mono {g g' n : Nat} {e : Exp} (hle : g ≤ g')
    (h : interp g n e ≠ .outOfGas) : interp g' n e = interp g n e := by
  induction g generalizing g' n e with
  | zero => simp [interp] at h
  | succ g ih =>
    obtain ⟨g', rfl⟩ : ∃ g'', g' = g'' + 1 := ⟨g' - 1, by omega⟩
    have hle' : g ≤ g' := by omega
    -- one sub-run (the head of a `bind` chain) is settled, so it is unchanged
    have hb : ∀ {n e} {k k' : Val → Nat → Result},
        (interp g n e).bind k ≠ .outOfGas →
        (∀ v m, interp g n e = .ok (.val v m) → k v m ≠ .outOfGas → k' v m = k v m) →
        (interp g' n e).bind k' = (interp g n e).bind k := by
      intro n e k k' hne hk
      obtain ⟨h₁, h₂⟩ := Result.bind_ne_outOfGas hne
      rw [ih hle' h₁]
      rcases hr : interp g n e with (⟨v, m⟩ | _) | _ | _
      · exact hk v m hr (h₂ v m hr)
      all_goals rfl
    cases e <;> simp only [interp] at h ⊢
    all_goals first
      | rfl
      | exact ih hle' h
      | skip
    case letin e₁ e₂ =>
      exact hb h fun v m _ h' => ih hle' h'
    case app e₁ e₂ =>
      refine hb h fun v m _ h' => hb h' fun va m' _ h'' => ?_
      rcases hap : v.apply va with _ | body <;> simp only [hap] at h'' ⊢
      rcases m' with _ | m'
      · rfl
      · exact ih hle' h''
    case add | leq | and =>
      exact hb h fun v m _ h' => hb h' fun _ _ _ _ => rfl
    case not | pair | ctor =>
      first
        | exact hb h fun _ _ _ _ => rfl
        | exact hb h fun v m _ h' => hb h' fun _ _ _ _ => rfl
    case ite e₀ e₁ e₂ =>
      refine hb h fun v m _ h' => ?_
      rcases v with _ | (_ | _) | _ | _ | _ | _ <;> simp_all <;> exact ih hle' h'
    case split e₁ e₂ =>
      refine hb h fun v m _ h' => ?_
      rcases v with _ | _ | _ | _ | _ | _ <;> simp_all <;> exact ih hle' h'
    case case e m alts =>
      refine hb h fun v k _ h' => ?_
      rcases v with _ | _ | _ | _ | _ | ⟨C, j, w⟩ <;> simp only at h' ⊢
      by_cases hj : j < m
      · simp only [hj, ↓reduceDIte] at h' ⊢
        rcases k with _ | k
        · rfl
        · exact ih hle' h'
      · simp [hj]

/-- Soundness: an outcome the interpreter returns is derivable. -/
theorem interp_sound {g n : Nat} {e : Exp} {o : Outcome}
    (h : interp g n e = .ok o) : Eval n e o := by
  induction g generalizing n e o with
  | zero => simp [interp] at h
  | succ g ih =>
    cases e <;> simp only [interp, Result.ok.injEq, reduceCtorEq] at h
    all_goals try (subst h; constructor)
    case ann | tabs | tapp => constructor; exact ih h
    case letin e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨v, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · exact .letin (ih h₁) (ih h₂)
      · exact .letin_to (ih h₁)
    case app e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨f, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · rcases Result.bind_eq_ok.mp h₂ with ⟨va, m', h₃, h₄⟩ | ⟨h₃, rfl⟩
        · rcases hf : f.apply va with _ | body <;> rw [hf] at h₄
          · simp at h₄
          · rcases m' with _ | m' <;> simp only [Result.ok.injEq] at h₄
            · subst h₄; exact .app_tick (ih h₁) (ih h₃) hf
            · exact .app (ih h₁) (ih h₃) hf (ih h₄)
        · exact .app_to₂ (ih h₁) (ih h₃)
      · exact .app_to₁ (ih h₁)
    case add e₁ e₂ | and e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨v₁, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · rcases Result.bind_eq_ok.mp h₂ with ⟨v₂, m', h₃, h₄⟩ | ⟨h₃, rfl⟩
        · split at h₄ <;> simp only [Result.ok.injEq, reduceCtorEq] at h₄
          subst h₄; constructor <;> first | exact ih h₁ | exact ih h₃
        · first | exact .add_to₂ (ih h₁) (ih h₃) | exact .and_to₂ (ih h₁) (ih h₃)
      · first | exact .add_to₁ (ih h₁) | exact .and_to₁ (ih h₁)
    case leq e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨v₁, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · rcases Result.bind_eq_ok.mp h₂ with ⟨v₂, m', h₃, h₄⟩ | ⟨h₃, rfl⟩
        · rcases hc : Val.leb? v₁ v₂ with _ | c <;> rw [hc] at h₄ <;>
            simp only [Result.ok.injEq, reduceCtorEq] at h₄
          subst h₄; exact .leq (ih h₁) (ih h₃) hc
        · exact .leq_to₂ (ih h₁) (ih h₃)
      · exact .leq_to₁ (ih h₁)
    case not e =>
      rcases Result.bind_eq_ok.mp h with ⟨v, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · split at h₂ <;> simp only [Result.ok.injEq, reduceCtorEq] at h₂
        subst h₂; exact .not_ (ih h₁)
      · exact .not_to (ih h₁)
    case ite e₀ e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨v, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · split at h₂
        · exact .ite_t (ih h₁) (ih h₂)
        · exact .ite_f (ih h₁) (ih h₂)
        · simp at h₂
      · exact .ite_to (ih h₁)
    case pair e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨v₁, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · rcases Result.bind_eq_ok.mp h₂ with ⟨v₂, m', h₃, h₄⟩ | ⟨h₃, rfl⟩
        · simp only [Result.ok.injEq] at h₄; subst h₄; exact .pair (ih h₁) (ih h₃)
        · exact .pair_to₂ (ih h₁) (ih h₃)
      · exact .pair_to₁ (ih h₁)
    case split e₁ e₂ =>
      rcases Result.bind_eq_ok.mp h with ⟨v, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · split at h₂
        · exact .split (ih h₁) (ih h₂)
        · simp at h₂
      · exact .split_to (ih h₁)
    case ctor C j τs e =>
      rcases Result.bind_eq_ok.mp h with ⟨w, m, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · simp only [Result.ok.injEq] at h₂; subst h₂; exact .ctor (ih h₁)
      · exact .ctor_to (ih h₁)
    case case e m alts =>
      rcases Result.bind_eq_ok.mp h with ⟨v, k, h₁, h₂⟩ | ⟨h₁, rfl⟩
      · rcases v with _ | _ | _ | _ | _ | ⟨C, j, w⟩ <;> simp only [reduceCtorEq] at h₂
        split at h₂
        · rename_i hj
          rcases k with _ | k <;> simp only [Result.ok.injEq] at h₂
          · subst h₂; exact .case_tick hj (ih h₁)
          · exact .case hj (ih h₁) (ih h₂)
        · simp at h₂
      · exact .case_to (ih h₁)

/-- A decided result stays decided with more gas. -/
theorem interp_up {g g' n : Nat} {e : Exp} {o : Outcome} (hle : g ≤ g')
    (h : interp g n e = .ok o) : interp g' n e = .ok o :=
  (interp_mono hle (by simp [h])).trans h

/-- Completeness: a derivable outcome is returned, given enough gas. -/
theorem interp_complete {n : Nat} {e : Exp} {o : Outcome}
    (h : Eval n e o) : ∃ g, interp g n e = .ok o := by
  induction h with
  | iconst | bconst | lam | fix => exact ⟨1, rfl⟩
  | ann _ ih | tabs _ ih | tapp _ ih | letin_to _ ih | app_to₁ _ ih | add_to₁ _ ih
  | leq_to₁ _ ih | not_to _ ih | and_to₁ _ ih | ite_to _ ih | pair_to₁ _ ih | split_to _ ih
  | ctor_to _ ih | case_to _ ih | not_ _ ih | ctor _ ih =>
    obtain ⟨g, hg⟩ := ih; exact ⟨g + 1, by simp [interp, hg]⟩
  | case_tick hj _ ih =>
    obtain ⟨g, hg⟩ := ih; exact ⟨g + 1, by simp [interp, hg, hj]⟩
  | letin _ _ ih₁ ih₂ | app_to₂ _ _ ih₁ ih₂ | add_to₂ _ _ ih₁ ih₂ | leq_to₂ _ _ ih₁ ih₂
  | and_to₂ _ _ ih₁ ih₂ | pair_to₂ _ _ ih₁ ih₂ | add _ _ ih₁ ih₂ | and_ _ _ ih₁ ih₂
  | pair _ _ ih₁ ih₂ | ite_t _ _ ih₁ ih₂ | ite_f _ _ ih₁ ih₂ | split _ _ ih₁ ih₂ =>
    obtain ⟨g₁, h₁⟩ := ih₁; obtain ⟨g₂, h₂⟩ := ih₂
    exact ⟨g₁ + g₂ + 1, by
      simp [interp, interp_up (by omega : g₁ ≤ g₁ + g₂) h₁, interp_up (by omega : g₂ ≤ g₁ + g₂) h₂]⟩
  | app_tick _ _ hap ih₁ ih₂ | leq _ _ hap ih₁ ih₂ =>
    obtain ⟨g₁, h₁⟩ := ih₁; obtain ⟨g₂, h₂⟩ := ih₂
    exact ⟨g₁ + g₂ + 1, by
      simp [interp, interp_up (by omega : g₁ ≤ g₁ + g₂) h₁, interp_up (by omega : g₂ ≤ g₁ + g₂) h₂,
        hap]⟩
  | case hj _ _ ih₁ ih₂ =>
    obtain ⟨g₁, h₁⟩ := ih₁; obtain ⟨g₂, h₂⟩ := ih₂
    exact ⟨g₁ + g₂ + 1, by
      simp [interp, interp_up (by omega : g₁ ≤ g₁ + g₂) h₁, interp_up (by omega : g₂ ≤ g₁ + g₂) h₂,
        hj]⟩
  | app _ _ hap _ ih₁ ih₂ ih₃ =>
    obtain ⟨g₁, h₁⟩ := ih₁; obtain ⟨g₂, h₂⟩ := ih₂; obtain ⟨g₃, h₃⟩ := ih₃
    exact ⟨g₁ + g₂ + g₃ + 1, by
      simp [interp, interp_up (by omega : g₁ ≤ g₁ + g₂ + g₃) h₁,
        interp_up (by omega : g₂ ≤ g₁ + g₂ + g₃) h₂, interp_up (by omega : g₃ ≤ g₁ + g₂ + g₃) h₃,
        hap]⟩

/-- The interpreter computes exactly the derivable outcomes. -/
theorem interp_iff {n : Nat} {e : Exp} {o : Outcome} :
    (∃ g, interp g n e = .ok o) ↔ Eval n e o :=
  ⟨fun ⟨_, h⟩ => interp_sound h, interp_complete⟩

/-- When the interpreter reports `stuck`, no outcome is derivable. -/
theorem interp_stuck {g n : Nat} {e : Exp} (h : interp g n e = .stuck) :
    ¬ ∃ o, Eval n e o := by
  rintro ⟨o, hev⟩
  obtain ⟨g', hg'⟩ := interp_complete hev
  have h₁ := interp_mono (Nat.le_add_right g g') (n := n) (e := e) (by simp [h])
  have h₂ := interp_up (Nat.le_add_left g' g) hg'
  rw [h, h₂] at h₁; cases h₁

/-- The interpreter never contradicts itself across gas budgets. -/
theorem interp_det {g g' n : Nat} {e : Exp} {r r' : Result}
    (h : interp g n e = r) (h' : interp g' n e = r')
    (hr : r ≠ .outOfGas) (hr' : r' ≠ .outOfGas) : r = r' := by
  have h₁ := interp_mono (Nat.le_add_right g g') (h ▸ hr)
  have h₂ := interp_mono (Nat.le_add_left g' g) (h' ▸ hr')
  rw [← h, ← h', ← h₁, h₂]

/-! ## Running programs -/

theorem runI_sound {g n : Nat} {e : Exp} {o : Outcome} (h : runI g n e = .ok o) : Run n e o :=
  interp_sound h

theorem runI_iff {n : Nat} {e : Exp} {o : Outcome} : (∃ g, runI g n e = .ok o) ↔ Run n e o :=
  interp_iff

theorem runI_stuck {g n : Nat} {e : Exp} (h : runI g n e = .stuck) : ¬ ∃ o, Run n e o :=
  interp_stuck h

end STLC

/-! ## Tactics

  `by_interp` proves `Eval n e o` or `Run n e o` for a concrete program by
  running the interpreter; `stuck_interp` proves `¬ ∃ o, Eval n e o` (or
  `Run`). The gas is generous: it bounds only the interpreter's recursion
  depth, and unused gas costs nothing. -/

macro "by_interp" : tactic => `(tactic| first
  | exact runI_sound (g := 100000) (by rfl)
  | exact interp_sound (g := 100000) (by rfl)
  | exact ⟨_, runI_sound (g := 100000) (by rfl)⟩
  | exact ⟨_, interp_sound (g := 100000) (by rfl)⟩)

macro "stuck_interp" : tactic => `(tactic| first
  | exact runI_stuck (g := 100000) (by rfl)
  | exact interp_stuck (g := 100000) (by rfl))

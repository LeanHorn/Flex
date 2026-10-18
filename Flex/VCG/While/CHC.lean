import Flex.VCG.While.Hoare
import Flex.VCG.While.Tactics
import Flex.VCG.While.Notation
import Flex.Tactic

/-! # Constrained Horn Clause Generation

  `whileCHC readOnlyVars inScope pre c post` produces a Lean Prop that is a system of
  Constrained Horn Clauses.  `readOnlyVars` are fixed variables available throughout (e.g.,
  loop bounds, input parameters).  `inScope` tracks currently available variables,
  expanding dynamically as new variables are assigned within the command.

  Every existential — both `seq` midpoints and `cwhile` invariants — has type
  `NaryProp inScope.length` (or a derived scope), yielding one argument per variable
  currently in scope.  The result is directly solvable by `solve_fixpoint`.

  Soundness: if the CHC system is satisfiable, then `ValidHoareTriple pre c post`.
-/

/-- CPS weakest-precondition VC generator.  `k` receives the *weakest
    precondition* of `c` w.r.t. `post`.  The ONLY existential introduced is the
    invariant of each `cwhile`: `seq` midpoints are *computed* by backward
    substitution, not guessed.  (Standard `pre`/`ic`/`vc` VC-gen — only the loop
    invariant is a genuine unknown.) -/
@[simp]
def vcGen (inScope : List CVar) (consts : List (State → Int)) (c : Cmd) (post : Assertion)
    (k : Assertion → Prop) : Prop :=
  match c with
  | .skip =>
    k post

  | .assign x f =>
    k (fun s => post (s[x ↦ f s]))

  | .seq c₁ c₂ =>
    let midScope := (inScope ++ c₁.assignedVars).eraseDups
    vcGen midScope consts c₂ post (fun mid => vcGen inScope consts c₁ mid k)

  | .ite g c₁ c₂ =>
    vcGen inScope consts c₁ post (fun wp₁ =>
      vcGen inScope consts c₂ post (fun wp₂ =>
        k (fun s => (g s = true → wp₁ s) ∧ (g s = false → wp₂ s))))

  | .cwhile g body =>
    let bodyScope := (inScope ++ body.assignedVars).eraseDups
    ∃ κ : NaryProp (inScope.length + consts.length),
        vcGen bodyScope consts body (applyNaryConsts inScope consts κ)
          (fun wpBody => ∀ s, applyNaryConsts inScope consts κ s ∧ g s = true → wpBody s)   -- preserve
      ∧ (∀ s, applyNaryConsts inScope consts κ s ∧ g s = false → post s)                    -- exit
      ∧ k (applyNaryConsts inScope consts κ)                                                -- wp(while) = inv

/-- Top-level VC: the precondition must imply the weakest precondition of `c`. -/
@[simp]
def whileCHC (inScope : List CVar) (consts : List (State → Int))
    (pre : Assertion) (c : Cmd) (post : Assertion) : Prop :=
  vcGen inScope consts c post (fun wp => ∀ s, pre s → wp s)

/-- Generic soundness of the CPS generator: a satisfied `vcGen` yields a weakest
    precondition `wp` with `{wp} c {post}` and `k wp`. -/
theorem vcGen_sound (inScope : List CVar) (consts : List (State → Int)) (c : Cmd)
    (post : Assertion) (k : Assertion → Prop) :
    vcGen inScope consts c post k → ∃ wp : Assertion, ValidHoareTriple wp c post ∧ k wp := by
  induction c generalizing inScope post k with
  | skip =>
    intro h; exact ⟨post, hoare_skip, h⟩
  | assign x f =>
    intro h; exact ⟨_, hoare_assign, h⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    intro h; simp only [vcGen] at h
    obtain ⟨wp₂, ht₂, h₁⟩ := ih₂ _ _ _ h
    obtain ⟨wp₁, ht₁, hk⟩ := ih₁ _ _ _ h₁
    exact ⟨wp₁, hoare_seq ht₁ ht₂, hk⟩
  | ite g c₁ c₂ ih₁ ih₂ =>
    intro h; simp only [vcGen] at h
    obtain ⟨wp₁, ht₁, h₂⟩ := ih₁ _ _ _ h
    obtain ⟨wp₂, ht₂, hk⟩ := ih₂ _ _ _ h₂
    refine ⟨fun s => (g s = true → wp₁ s) ∧ (g s = false → wp₂ s), ?_, hk⟩
    exact hoare_if (hoare_consequence_pre ht₁ (fun s hs => hs.1.1 hs.2))
                   (hoare_consequence_pre ht₂ (fun s hs => hs.1.2 hs.2))
  | cwhile g body ih =>
    intro h; simp only [vcGen] at h
    obtain ⟨κ, hbody, hexit, hk⟩ := h
    obtain ⟨wpBody, htBody, hpres⟩ := ih _ _ _ hbody
    exact ⟨applyNaryConsts inScope consts κ,
           hoare_while (fun _ hp => hp) (hoare_consequence_pre htBody hpres) hexit,
           hk⟩

/-- Soundness: if the CHC system is satisfiable, the Hoare triple holds. -/
theorem whileCHC_sound (inScope : List CVar) (consts : List (State → Int))
    (pre : Assertion) (c : Cmd) (post : Assertion) :
    whileCHC inScope consts pre c post → ValidHoareTriple pre c post := by
  intro h
  obtain ⟨wp, htriple, hk⟩ := vcGen_sound inScope consts c post _ h
  exact hoare_consequence_pre htriple hk

/-! # Examples -/

-- Program: x := 0; while x < n do x := x + 1 end
-- Pre: 0 ≤ n, Post: x = n
abbrev countToN : Cmd :=
  <| x := 0 ; while x < n do x := x + 1 |>

@[qualif] def Le (i1 i2 : Int) : Prop := i1 ≤ i2

-- vars=["n","x"]: inScope expands from ["n"] to ["n","x"] after first assignment
example : {| 0 ≤ n |} countToN {| x = n |} := by
  generate
  fix

-- Program: while x ≠ 0 do x := x - 1 end
-- Pre: True, Post: x = 0
@[simp]
def reduceToZero : Cmd :=
  <| while x != 0 do x := x - 1 |>

-- x is pre-existing variable (in readOnlyVars); inScope stays ["x"]
theorem reduceToZero_correct :
    {| ⊤ |} reduceToZero {| x = 0 |} := by
  generate
  fix

@[qualif]
def sumEq (i1 i2 i3 : Int) : Prop :=
  i1 + i2 = i3

@[qualif]
def sumEq1 (i1 i2 i3 : Int) : Prop :=
  i1 + (i2 + 1) = i3

@[qualif]
def Ge0 (i1 : Int) : Prop :=
  0 ≤ i1

-- Program: x := n; y := 0; while x ≠ 0 do x := x-1; y := y+1 end
-- Pre: 0 ≤ n, Post: y = n
-- vars=["n","x","y"]: every ∃ has type Int → Int → Int → Prop  (args: s "n", s "x", s "y")
abbrev slowAssign : Cmd :=
  <| x := n ; y := 0 ; while x != 0 do (x := x - 1 ; y := y + 1) |>

-- κ = fun nv xv yv => xv + yv = nv ∧ 0 ≤ xv
theorem slowAssign_correct :
    {| 0 ≤ n |} slowAssign {| y = n |} := by
  generate
  fix


@[grind]
def fib_spec (n : Int) : Int :=
  if n ≤ 1 then 1
  else fib_spec (n - 1) + fib_spec (n - 2)
termination_by n.toNat

@[qualif] def q_gt1 (a : Int) : Prop := a > 1
@[qualif] def q_eq_fib (v i : Int) : Prop := v = fib_spec i
@[qualif] def q_eq_fib_pred (v i : Int) : Prop := v = fib_spec (i - 1)

theorem fibLoop_correct (n : Int) :
  ⊧ (fun s => s "n" = n ∧ n ≥ 2)
    <| prev := 1; x := 2; i := 2;
    while i < n do (
      next := prev + x ;
      prev := x ;
      x := next ;
      i := i + 1) |>
  (fun s => s "x" = fib_spec n) := by
  generate
  fix

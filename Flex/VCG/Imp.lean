import Lean
import Flex.Tactic.Tactics.Hoist

/-! Typed Imp: safe partial correctness and existential loop invariants. -/

namespace Imp
universe u v

/-! ## Typed stores -/

/-- A typed store; expressions are ordinary Lean functions over this store. -/
def State : List Type → Type
  | [] => Unit
  | α :: Γ => α × State Γ

/-- Invariants take the store's fields as separate, typed arguments. -/
def Predicate : List Type → Type
  | [] => Prop
  | α :: Γ => α → Predicate Γ

def applyPredicate : {Γ : List Type} → Predicate Γ → State Γ → Prop
  | [], p, _ => p
  | _ :: _, p, (x, s) => applyPredicate (p x) s

def curryPredicate : {Γ : List Type} → (State Γ → Prop) → Predicate Γ
  | [], p => p ()
  | _ :: _, p => fun x => curryPredicate (fun s => p (x, s))

@[simp] theorem apply_curryPredicate {Γ : List Type} (p : State Γ → Prop) (s : State Γ) :
    applyPredicate (curryPredicate p) s = p s := by
  induction Γ with
  | nil => cases s; rfl
  | cons α Γ ih => exact ih (fun t => p (s.1, t)) s.2

@[simp] theorem curry_applyPredicate {Γ : List Type} (p : Predicate Γ) :
    curryPredicate (applyPredicate p) = p := by
  induction Γ with
  | nil => rfl
  | cons α Γ ih => funext x; exact ih (p x)

/-- A position in a typed store. -/
inductive Var : List Type → Type → Type 1 where
  | here : Var (α :: Γ) α
  | there : Var Γ α → Var (β :: Γ) α

def Var.get : Var Γ α → State Γ → α
  | .here, s => s.1
  | .there x, s => x.get s.2

def Var.set : Var Γ α → α → State Γ → State Γ
  | .here, v, s => (v, s.2)
  | .there x, v, s => (s.1, x.set v s.2)

@[simp] theorem Var.get_set (x : Var Γ α) (v : α) (s : State Γ) :
    x.get (x.set v s) = v := by
  induction x with
  | here => rfl
  | there x ih => exact ih v s.2

@[simp] theorem Var.set_get (x : Var Γ α) (s : State Γ) :
    x.set (x.get s) s = s := by
  induction x with
  | here => rfl
  | there x ih => exact congrArg (fun t => (s.1, t)) (ih s.2)

/-! ## Commands and safe partial correctness -/

abbrev Assertion (σ : Type u) := σ → Prop

inductive Cmd (σ : Type u) where
  | step (f : σ → Option σ)
  | seq (first second : Cmd σ)
  | branch (guard : σ → Bool) (yes no : Cmd σ)
  | loop (guard : σ → Bool) (body : Cmd σ)

def Cmd.skip : Cmd σ := .step some

def Cmd.modify (f : σ → σ) : Cmd σ := .step (fun s => some (f s))

def Cmd.assert (p : σ → Bool) : Cmd σ :=
  .step (fun s => if p s then some s else none)

/-- Assign a native Lean expression to a typed variable. -/
def Cmd.assign (x : Var Γ α) (e : State Γ → α) : Cmd (State Γ) :=
  .modify (fun s => x.set (e s) s)

/-- Finite executions return a state or a fault. -/
inductive Exec : Cmd σ → σ → Option σ → Prop where
  | step_ok {f s t} : f s = some t → Exec (.step f) s (some t)
  | step_fault {f s} : f s = none → Exec (.step f) s none
  | seq_ok {first second s t r} :
      Exec first s (some t) → Exec second t r → Exec (.seq first second) s r
  | seq_fault {first second s} :
      Exec first s none → Exec (.seq first second) s none
  | branch_true {guard yes no s r} :
      guard s = true → Exec yes s r → Exec (.branch guard yes no) s r
  | branch_false {guard yes no s r} :
      guard s = false → Exec no s r → Exec (.branch guard yes no) s r
  | loop_stop {guard body s} :
      guard s = false → Exec (.loop guard body) s (some s)
  | loop_next {guard body s t r} :
      guard s = true → Exec body s (some t) →
      Exec (.loop guard body) t r → Exec (.loop guard body) s r
  | loop_fault {guard body s} :
      guard s = true → Exec body s none → Exec (.loop guard body) s none

@[simp] theorem Exec.step_iff {f : σ → Option σ} {s : σ} {r : Option σ} :
    Exec (.step f) s r ↔ f s = r := by
  constructor
  · intro h
    cases h <;> assumption
  · intro h
    cases r with
    | none => exact .step_fault h
    | some t => exact .step_ok h

@[simp] theorem Exec.modify_iff {f : σ → σ} {s : σ} {r : Option σ} :
    Exec (.modify f) s r ↔ some (f s) = r :=
  Exec.step_iff

@[simp] theorem Exec.skip_iff {s : σ} {r : Option σ} :
    Exec .skip s r ↔ some s = r :=
  Exec.step_iff

/-- Executions cannot fault, and terminating executions satisfy `post`.
    Termination is not required. -/
def Valid (pre : Assertion σ) (cmd : Cmd σ) (post : Assertion σ) : Prop :=
  ∀ s r, pre s → Exec cmd s r →
    match r with
    | none => False
    | some t => post t

theorem Valid.consequence_pre {pre pre' post : Assertion σ} {cmd : Cmd σ}
    (h : Valid pre' cmd post) (hpre : ∀ s, pre s → pre' s) :
    Valid pre cmd post := by
  intro s r hs hr
  exact h s r (hpre s hs) hr

theorem Valid.no_fault {pre post : Assertion σ} {cmd : Cmd σ}
    (h : Valid pre cmd post) {s : σ} (hs : pre s) : ¬ Exec cmd s none :=
  fun hr => h s none hs hr

theorem Valid.loop {inv post : Assertion σ} {guard : σ → Bool} {body : Cmd σ}
    (hbody : Valid (fun s => inv s ∧ guard s = true) body inv)
    (hexit : ∀ s, inv s → guard s = false → post s) :
    Valid inv (.loop guard body) post := by
  intro s r hs hr
  revert hs
  generalize hcmd : Cmd.loop guard body = cmd at hr
  induction hr with
  | loop_stop hg =>
      intro hi
      cases hcmd
      exact hexit _ hi hg
  | loop_next hg hb _ _ ih =>
      intro hi
      cases hcmd
      exact ih rfl (hbody _ _ ⟨hi, hg⟩ hb)
  | loop_fault hg hb _ =>
      intro hi
      cases hcmd
      exact hbody _ _ ⟨hi, hg⟩ hb
  | _ => intro; cases hcmd

/-! ## VC generation and soundness -/

/-- Backward VC generation; each loop introduces a fresh invariant. -/
def vcGen {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (cmd : Cmd σ) (post : Assertion σ) (k : Assertion σ → Prop) : Prop :=
  match cmd with
  | .step f => k (fun s => match f s with | none => False | some t => post t)
  | .seq first second =>
      vcGen holds second post (fun mid => vcGen holds first mid k)
  | .branch guard yes no =>
      vcGen holds yes post (fun yesPre =>
        vcGen holds no post (fun noPre =>
          k (fun s => (guard s = true → yesPre s) ∧ (guard s = false → noPre s))))
  | .loop guard body =>
      ∃ inv : ι,
        vcGen holds body (holds inv) (fun wp => ∀ s, holds inv s → guard s = true → wp s) ∧
        (∀ s, holds inv s → guard s = false → post s) ∧ k (holds inv)

@[simp] theorem vcGen_step {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (f : σ → Option σ) (post : Assertion σ) (k : Assertion σ → Prop) :
    vcGen holds (.step f) post k =
      k (fun s => match f s with | none => False | some t => post t) := rfl

@[simp] theorem vcGen_modify {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (f : σ → σ) (post : Assertion σ) (k : Assertion σ → Prop) :
    vcGen holds (.modify f) post k = k (fun s => post (f s)) := rfl

@[simp] theorem vcGen_skip {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (post : Assertion σ) (k : Assertion σ → Prop) :
    vcGen holds .skip post k = k post := rfl

@[simp] theorem vcGen_assert {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (p : σ → Bool) (post : Assertion σ) (k : Assertion σ → Prop) :
    vcGen holds (.assert p) post k = k (fun s => p s = true ∧ post s) := by
  simp only [Cmd.assert, vcGen]
  congr 1
  funext s
  cases p s <;> simp

def chc {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (pre : Assertion σ) (cmd : Cmd σ) (post : Assertion σ) : Prop :=
  vcGen holds cmd post (fun wp => ∀ s, pre s → wp s)

theorem vcGen_sound {σ : Type u} {ι : Type v} (holds : ι → Assertion σ)
    (cmd : Cmd σ) (post : Assertion σ) (k : Assertion σ → Prop) :
    vcGen holds cmd post k → ∃ pre, k pre ∧ Valid pre cmd post := by
  induction cmd generalizing post k with
  | step f =>
      intro hk
      refine ⟨_, hk, ?_⟩
      intro s r hs hr
      cases hr with
      | step_ok heq => simpa [heq] using hs
      | step_fault heq => simp [heq] at hs
  | seq first second ihFirst ihSecond =>
      intro h
      obtain ⟨mid, hfirst, hsecond⟩ := ihSecond _ _ h
      obtain ⟨pre, hk, hfirst⟩ := ihFirst _ _ hfirst
      refine ⟨pre, hk, ?_⟩
      intro s r hs hr
      cases hr with
      | seq_ok h₁ h₂ => exact hsecond _ _ (hfirst _ _ hs h₁) h₂
      | seq_fault h₁ => exact hfirst _ _ hs h₁
  | branch guard yes no ihYes ihNo =>
      intro h
      obtain ⟨yesPre, hno, hyes⟩ := ihYes _ _ h
      obtain ⟨noPre, hk, hno⟩ := ihNo _ _ hno
      refine ⟨_, hk, ?_⟩
      intro s r hs hr
      cases hr with
      | branch_true hg hb => exact hyes _ _ (hs.1 hg) hb
      | branch_false hg hb => exact hno _ _ (hs.2 hg) hb
  | loop guard body ih =>
      rintro ⟨inv, hbody, hexit, hk⟩
      obtain ⟨wp, hpre, hbody⟩ := ih _ _ hbody
      refine ⟨holds inv, hk, Valid.loop ?_ hexit⟩
      exact hbody.consequence_pre (fun s hs => hpre s hs.1 hs.2)

theorem chc_sound {σ : Type u} {ι : Type v} {holds : ι → Assertion σ}
    {pre post : Assertion σ} {cmd : Cmd σ} :
    chc holds pre cmd post → Valid pre cmd post := by
  intro h
  obtain ⟨wp, hpre, hvalid⟩ := vcGen_sound holds cmd post _ h
  exact hvalid.consequence_pre hpre

/-- Generate CHCs with a curried invariant for each loop. -/
def generate {Γ : List Type} (pre : Assertion (State Γ))
    (cmd : Cmd (State Γ)) (post : Assertion (State Γ)) : Prop :=
  chc (@applyPredicate Γ) pre cmd post

theorem generate_sound {Γ : List Type} {pre post : Assertion (State Γ)}
    {cmd : Cmd (State Γ)} : generate pre cmd post → Valid pre cmd post :=
  chc_sound

/-! ## Fuel-bounded execution -/

inductive RunResult (σ : Type u) where
  | done (state : σ)
  | fault
  | timeout
  deriving Repr

/-- Fuel bounds interpreter recursion; exhaustion is distinct from a program fault. -/
def Cmd.run : Nat → Cmd σ → σ → RunResult σ
  | 0, _, _ => .timeout
  | _ + 1, .step f, s =>
      match f s with
      | some t => .done t
      | none => .fault
  | fuel + 1, .seq first second, s =>
      match first.run fuel s with
      | .done t => second.run fuel t
      | .fault => .fault
      | .timeout => .timeout
  | fuel + 1, .branch guard yes no, s =>
      (if guard s then yes else no).run fuel s
  | fuel + 1, .loop guard body, s =>
      if guard s then
        match body.run fuel s with
        | .done t => (Cmd.loop guard body).run fuel t
        | .fault => .fault
        | .timeout => .timeout
      else .done s

/-- Every completed interpreter run agrees with the operational semantics. -/
theorem Cmd.run_sound (fuel : Nat) (cmd : Cmd σ) (s : σ) :
    match cmd.run fuel s with
    | .done t => Exec cmd s (some t)
    | .fault => Exec cmd s none
    | .timeout => True := by
  induction fuel generalizing cmd s with
  | zero => trivial
  | succ fuel ih =>
      cases cmd with
      | step f =>
          simp only [Cmd.run]
          cases h : f s with
          | none => exact Exec.step_fault h
          | some t => exact Exec.step_ok h
      | seq first second =>
          have hfirst := ih first s
          cases h : first.run fuel s with
          | timeout => simp [Cmd.run, h]
          | fault =>
              simp only [Cmd.run, h]
              exact Exec.seq_fault (by simpa [h] using hfirst)
          | done t =>
              have hsecond := ih second t
              simp only [Cmd.run, h]
              cases h₂ : second.run fuel t with
              | timeout => trivial
              | fault => exact Exec.seq_ok (by simpa [h] using hfirst) (by simpa [h₂] using hsecond)
              | done u => exact Exec.seq_ok (by simpa [h] using hfirst) (by simpa [h₂] using hsecond)
      | branch guard yes no =>
          cases h : guard s with
          | false =>
              have hb := ih no s
              simp only [Cmd.run, h, Bool.false_eq_true, ↓reduceIte]
              cases hr : no.run fuel s with
              | timeout => trivial
              | fault => exact Exec.branch_false h (by simpa [hr] using hb)
              | done t => exact Exec.branch_false h (by simpa [hr] using hb)
          | true =>
              have hb := ih yes s
              simp only [Cmd.run, h, ↓reduceIte]
              cases hr : yes.run fuel s with
              | timeout => trivial
              | fault => exact Exec.branch_true h (by simpa [hr] using hb)
              | done t => exact Exec.branch_true h (by simpa [hr] using hb)
      | loop guard body =>
          cases h : guard s with
          | false =>
              simp only [Cmd.run, h, Bool.false_eq_true, ↓reduceIte]
              exact Exec.loop_stop h
          | true =>
              have hb := ih body s
              simp only [Cmd.run, h, ↓reduceIte]
              cases hr : body.run fuel s with
              | timeout => trivial
              | fault => exact Exec.loop_fault h (by simpa [hr] using hb)
              | done t =>
                  dsimp only
                  have hl := ih (.loop guard body) t
                  cases hlr : (Cmd.loop guard body).run fuel t with
                  | timeout => trivial
                  | fault => exact Exec.loop_next h (by simpa [hr] using hb) (by simpa [hlr] using hl)
                  | done u => exact Exec.loop_next h (by simpa [hr] using hb) (by simpa [hlr] using hl)

end Imp

/-! ## Program notation -/

declare_syntax_cat impCmd
syntax "set" "(" term,* ")" : impCmd
syntax "modify" term : impCmd
syntax "step" term : impCmd
syntax "call" term : impCmd
syntax "assert" term : impCmd
syntax "skip" : impCmd
syntax:10 impCmd:11 ";" impCmd:10 : impCmd
syntax:20 "while" termBeforeDo "do" "{" impCmd "}" : impCmd
syntax:20 "if" term "then" "{" impCmd "}" "else" "{" impCmd "}" : impCmd

/-- Named state fields in guards and simultaneous assignments; expressions are Lean terms. -/
syntax "imp" "(" ident,+ ")" "{" impCmd "}" : term

namespace Imp
open Lean

private def tuple (fields : Array (TSyntax `term)) (tail : TSyntax `term) :
    MacroM (TSyntax `term) :=
  fields.foldrM (fun field rest => `(($field, $rest))) tail

private partial def expandCmd (vars : Array Ident) (cmd : TSyntax `impCmd) :
    MacroM (TSyntax `term) := do
  let fields := vars.map fun v => (⟨(mkIdent v.getId).raw⟩ : TSyntax `term)
  let pattern ← tuple fields (← `(_))
  match cmd with
  | `(impCmd| set ($values:term,*)) =>
      unless values.getElems.size == vars.size do
        Macro.throwErrorAt cmd "set must supply one value per state variable"
      let result ← tuple values.getElems (← `(()))
      `(Imp.Cmd.modify (fun $pattern => $result))
  | `(impCmd| modify $f:term) => `(Imp.Cmd.modify $f)
  | `(impCmd| step $f:term) => `(Imp.Cmd.step $f)
  | `(impCmd| call $cmd:term) => pure cmd
  | `(impCmd| assert $p:term) => `(Imp.Cmd.assert (fun $pattern => $p))
  | `(impCmd| skip) => `(Imp.Cmd.skip)
  | `(impCmd| $first:impCmd; $second:impCmd) => do
      let first ← expandCmd vars first
      let second ← expandCmd vars second
      `(Imp.Cmd.seq $first $second)
  | `(impCmd| while $guard:term do { $body:impCmd }) => do
      let body ← expandCmd vars body
      `(Imp.Cmd.loop (fun $pattern => $guard) $body)
  | `(impCmd| if $guard:term then { $yes:impCmd } else { $no:impCmd }) => do
      let yes ← expandCmd vars yes
      let no ← expandCmd vars no
      `(Imp.Cmd.branch (fun $pattern => $guard) $yes $no)
  | _ => Macro.throwUnsupported

macro_rules
  | `(imp ($vars:ident,*) { $body:impCmd }) => do
      let vars := vars.getElems
      let names := vars.map (·.getId)
      unless names.toList.eraseDups.length == names.size do
        Macro.throwError "imp state variables must have distinct names"
      expandCmd vars body

end Imp

/-! ## Exposing generated CHCs -/

open Lean Meta Elab Tactic

namespace Imp

private theorem forallUnit (p : Unit → Prop) : (∀ u, p u) ↔ p () := by
  constructor
  · exact fun h => h ()
  · intro h u; cases u; exact h

/-- An optional step must succeed, and its result must satisfy the continuation. -/
private theorem checkStep (x : Option α) (p : α → Prop) :
    (match x with | none => False | some y => p y) ↔
      x ≠ none ∧ ∀ y, x = some y → p y := by
  cases x <;> simp

private partial def programDefinitions (root : Name) (e : Expr)
    (seen : NameSet := {}) : MetaM NameSet := do
  let mut seen := seen
  for name in e.getUsedConstants do
    if root.isPrefixOf name && !seen.contains name then
      if let .defnInfo info ← getConstInfo name then
        seen ← programDefinitions root info.value (seen.insert name)
  return seen

/-- Expose a generated VC, preserving its existential invariants and obligations. -/
def prepare : TacticM Unit := do
  evalTactic (← `(tactic| intros))
  withMainContext do
    let mut target ← (← getMainGoal).getType
    let some name := target.getAppFn.constName?
      | throwError "imp_prepare: expected a named generated VC"
    let root := name.getRoot
    let mut defs : NameSet := {}
    for _ in [:20] do
      if target.isAppOf ``Imp.generate then break
      let some name := target.getAppFn.constName?
        | throwError "imp_prepare: expected an Imp.generate application"
      defs := defs.insert name
      let some next ← unfoldDefinition? target
        | throwError "Imp preparation: expected an Imp.generate application"
      target := next.headBeta
    unless target.isAppOf ``Imp.generate do
      throwError "Imp preparation: could not expose Imp.generate"
    let args := target.getAppArgs
    let pre := args[args.size - 3]!
    let cmd := args[args.size - 2]!
    let post := args[args.size - 1]!
    defs ← programDefinitions root cmd defs
    for assertion in #[pre, post] do
      if let .const name _ := assertion.getAppFn then
        defs := defs.insert name
    let names := defs.toArray.map mkIdent
    evalTactic (← `(tactic|
      simp only [$[$names:ident],*, Imp.generate, Imp.chc, Imp.vcGen,
        Imp.Cmd.modify, Imp.Cmd.skip, Imp.Cmd.assert,
        Imp.State, Imp.Predicate, Imp.applyPredicate, Prod.forall, forallUnit]))
    evalTactic (← `(tactic| simp (config := { failIfUnchanged := false })
      only [checkStep, Prod.forall, forallUnit]))
    -- Preserve data binders and source observations for qualifier scraping.
    evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only
      [true_implies, false_implies, true_and, and_true, false_and, and_false, forall_const,
       decide_eq_true_eq, decide_eq_false_iff_not, Option.some_ne_none,
       Option.some.injEq, Prod.mk.injEq, Bool.not_eq, Bool.not_eq_true,
       Bool.not_eq_false, List.isEmpty_iff, List.isEmpty_eq_false_iff]))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| hoist_exists))

elab "imp_prepare" : tactic => prepare

end Imp

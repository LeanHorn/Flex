import Flex.VCG.SystemFRK

/-! Adversarial checks for the current SystemFRK definitions.
Regression checks reject definition defects and certify the repaired
completeness counterexamples. No solver is used. Run `lake env lean eval/SystemFRKAudit.lean`.
-/
namespace SystemFRK.Adversarial
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

macro "compute_frk" : tactic => `(tactic| (cbv; repeat first
  | rw [checkFuel.eq_def]; cbv
  | rw [synthFuel.eq_def]; cbv
  | rw [subtype.eq_def]; cbv))

-- A closed integer receives a refinement with an unbound logical name.
def dangling : Formula := .eq (.var "missing") (.var "missing")
def danglingType : Ty := .refine .int (.theory (.or dangling (.not dangling)))

theorem dangling_untypable (s : Signature) (m : DataModel) (k : KAssignment)
    (expression : Expr) :
    ¬ HasType s m k {} [] expression danglingType := by
  intro typed
  have formed := typed.wellFormed
  have rejected : wfTy s {} 512 danglingType = .error "unbound logical variable 'missing'" := by
    compute_frk
  rw [rejected] at formed
  contradiction

theorem dangling_not_scoped : ¬ danglingType.InScope {} := by
  simp [danglingType, dangling, Ty.InScope, Ty.TypeScoped, Ty.freeVars,
    Atom.freeVars, Formula.freeVars, LTerm.freeVars, Context.names, valueName]

example : wfTy {} {} 512 danglingType = .error "unbound logical variable 'missing'" := by
  compute_frk

-- Negation turns failure to evaluate an undeclared measure into a true refinement.
def missingObservation : LTerm := .measure "missingMeasure" (.int 0)
def missingMeasureType : Ty :=
  .refine .int (.theory (.not (.eq missingObservation missingObservation)))

theorem missing_measure_never_evaluates (env : Environment) (value : Value) :
    ¬ LogicalEval {} env missingObservation value := by
  intro evaluated
  cases evaluated with
  | measure argument measured =>
    cases measured with
    | constructor found _ _ => simp [Signature.findMeasure] at found

theorem missing_measure_refinement_true (env : Environment) :
    (Formula.not (.eq missingObservation missingObservation)).denote {} env := by
  rintro ⟨value, evaluated, _⟩
  exact missing_measure_never_evaluates env value evaluated

theorem missing_measure_untypable (m : DataModel) (k : KAssignment) (expression : Expr) :
    ¬ HasType {} m k {} [] expression missingMeasureType := by
  intro typed
  have formed := typed.wellFormed
  have rejected : wfTy {} {} 512 missingMeasureType =
      .error "unknown measure 'missingMeasure'" := by compute_frk
  rw [rejected] at formed
  contradiction

example : wfTy {} {} 512 missingMeasureType = .error "unknown measure 'missingMeasure'" := by
  compute_frk

-- Invariant datatype arguments compare modulo binder renaming.
def boxSignature : Signature := {
  datatypes := [{
    name := "Box"
    params := 1
    ctors := [{ name := "box", fields := [.var 0] }]
  }]
}
def functionX : Ty := .arrow "x" .int .int
def functionY : Ty := .arrow "y" .int .int
def boxX : Ty := .data "Box" [functionX]
def boxY : Ty := .data "Box" [functionY]

theorem box_alpha_equivalent (s : Signature) (m : DataModel) (k : KAssignment)
    (types : TypeEnvironment) (env : Environment) :
    boxX.denote s m k types env = boxY.denote s m k types env := by
  simp [boxX, boxY, functionX, functionY, Ty.denote]

example : boxSignature.validate = .ok () := by compute_frk
example : wfTy boxSignature {} 512 boxX = .ok () := by compute_frk
example : wfTy boxSignature {} 512 boxY = .ok () := by compute_frk
private def actualVC (s : Signature) (e : Expr) (t : Ty) : Cstr :=
  match generate s e t with
  | .ok c => c
  | .error _ => .head (.theory .falsity)

macro "reduce_actual_vc" : tactic => `(tactic| (conv =>
  arg 3
  cbv
  repeat first
    | rw [checkFuel.eq_def]; cbv
    | rw [synthFuel.eq_def]; cbv
    | rw [subtype.eq_def]; cbv))

def boxIdentity : Expr := .lam "b" boxX (.var "b")
def boxIdentityTy : Ty := .arrow "b" boxY boxY
def boxVC : Cstr := actualVC boxSignature boxIdentity boxIdentityTy

theorem box_generated : generate boxSignature boxIdentity boxIdentityTy = .ok boxVC := by
  compute_frk

theorem box_vc_valid (k : KAssignment) : boxVC.Valid boxSignature k := by
  unfold boxVC
  reduce_actual_vc
  simp [Cstr.Valid, Cstr.denote]

-- Type substitution's own freshening also compares successfully.
def polyId : Expr := .tyLam (.lam "x" (.var 0) (.var "x"))
def instantiatedTy : Ty := .arrow "z" boxX boxX
def instantiatedVC : Cstr := actualVC boxSignature (.tyApp polyId boxX) instantiatedTy

theorem instantiated_generated :
    generate boxSignature (.tyApp polyId boxX) instantiatedTy = .ok instantiatedVC := by
  compute_frk

theorem instantiated_vc_valid (k : KAssignment) : instantiatedVC.Valid boxSignature k := by
  unfold instantiatedVC
  reduce_actual_vc
  simp [Cstr.Valid, Cstr.denote]

-- Dependencies, shadowing, and names resembling fresh binders must be preserved.
def dependentArrow (name : String) : Ty := .arrow name .int
  (.refine .int (.theory (.eq (.var valueName) (.var name))))
example : (dependentArrow "x").alphaEq 32 (dependentArrow "y") = true := by compute_frk
example : (Ty.arrow "x" .int (.arrow "x" .int (dependentArrow "z"))).alphaEq 32
    (.arrow "a" .int (.arrow "b" .int (dependentArrow "c"))) = true := by compute_frk
example : (Ty.arrow "x" .int (.refine .int (.theory (.eq (.var valueName) (.var "free"))))).alphaEq 32
    (dependentArrow "free") = false := by compute_frk
example : (dependentArrow "$alpha").alphaEq 32 (dependentArrow "x") = true := by compute_frk
example : (Ty.data "Box" [.int]).alphaEq 32
    (.data "Box" [.refine .int (.theory .truth)]) = false := by compute_frk
example : (Ty.data "Box" [.int]).alphaEq 32 (.data "Box" [.int, .int]) = false := by compute_frk
example : (Ty.data "Box" [.int]).alphaEq 32 (.data "Other" [.int]) = false := by compute_frk

def shadowedArrow (outer inner referred : String) : Ty :=
  .arrow outer .int (.arrow inner .int
    (.refine .int (.theory (.eq (.var valueName) (.var referred)))))
example : (shadowedArrow "x" "x" "x").alphaEq 32 (shadowedArrow "a" "b" "b") = true := by
  compute_frk
example : (shadowedArrow "x" "x" "x").alphaEq 32 (shadowedArrow "a" "b" "a") = false := by
  compute_frk
example : generate boxSignature (.lam "b" (.data "Box" [.int]) (.var "b"))
    (.arrow "b" (.data "Box" [.bool]) (.data "Box" [.bool])) =
      .error "datatype type arguments do not match" := by compute_frk

theorem instantiated_certified (k : KAssignment) :
    ∃ value, Eval boxSignature [] none (.tyApp polyId boxX) value ∧
      instantiatedTy.denote boxSignature (boxSignature.datatypeModel k) k [] [] value :=
  generated_total_correctness _ _ _ _ _ instantiated_generated (instantiated_vc_valid k)

-- Not all vacuous predicates are bugs: an unrealizable context has no executions to check.
theorem semantic_typing_vacuous_when_unscoped
    (s : Signature) (m : DataModel) (k : KAssignment)
    (ctx : Context) (unscoped : ¬ ctx.Scoped) (e : Expr) (t : Ty) :
    SemTyped s m k ctx [] e t := by
  intro hasScope
  exact (unscoped hasScope).elim


def cellSignature : Signature := {
  datatypes := [{
    name := "Cell"
    params := 0
    ctors := [{ name := "cell", fields := [.int] }]
  }]
  measures := [{
    name := "payload"
    datatype := "Cell"
    cases := [{ ctor := "cell", body := .field 0 }]
  }]
}
def cellTy : Ty := .data "Cell" []
def cellIdentity : Expr := .lam "c" cellTy (.var "c")
def cellIdentityTy : Ty := .arrow "c" cellTy
  (.refine cellTy (.theory (.eq
    (.measure "payload" (.var valueName)) (.measure "payload" (.var "c")))))

def oldCellVC : Cstr := .all "c" .value (.all "$g0" .value
  (.guard (.theory (.eq (.var "$g0") (.var "c")))
    (.head (.theory (.eq (.measure "payload" (.var "$g0"))
      (.measure "payload" (.var "c")))))))

theorem old_cell_vc_impossible (k : KAssignment) : ¬ oldCellVC.Valid cellSignature k := by
  intro valid
  have same : (Atom.theory (.eq (.var "$g0") (.var "c"))).denote cellSignature k
      [⟨"$g0", .int 0⟩, ⟨"c", .int 0⟩] :=
    ⟨.int 0, .var rfl, .var rfl⟩
  have head := valid [] (.int 0) True.intro (.int 0) True.intro same
  obtain ⟨value, observed, _⟩ := head
  cases observed with
  | measure argument measured =>
    have zero : LogicalEval cellSignature [⟨"$g0", .int 0⟩, ⟨"c", .int 0⟩]
        (.var "$g0") (.int 0) := .var rfl
    cases argument.deterministic zero
    cases measured

def cellVC : Cstr := .all "c" .value
  (.guard (.theory (.eq (.measure "payload" (.var "c")) (.measure "payload" (.var "c"))))
    (.all "$g0" .value (.guard (.theory (.eq (.var "$g0") (.var "c")))
      (.head (.theory (.eq (.measure "payload" (.var "$g0")) (.measure "payload" (.var "c"))))))))

theorem cell_generated : generate cellSignature cellIdentity cellIdentityTy = .ok cellVC := by
  compute_frk

theorem cell_vc_valid (k : KAssignment) : cellVC.Valid cellSignature k := by
  intro env c _ defined witness _ same
  obtain ⟨v, witnessEval, cEval⟩ := same
  have eqWitness : witness = v := by
    cases witnessEval with
    | var lookup => exact Option.some.inj lookup
  have eqC : c = v := by
    cases cEval with
    | var lookup => exact Option.some.inj lookup
  subst witness
  subst c
  obtain ⟨measuredValue, evaluated, _⟩ := defined
  cases evaluated with
  | measure arg measured =>
    have known : LogicalEval cellSignature (env.bind "c" v) (.var "c") v := .var rfl
    cases arg.deterministic known
    exact ⟨_, .measure (.var rfl) measured, .measure (.var rfl) measured⟩

theorem cell_certified (k : KAssignment) :
    ∃ value, Eval cellSignature [] none cellIdentity value ∧
      cellIdentityTy.denote cellSignature (cellSignature.datatypeModel k) k [] [] value :=
  generated_total_correctness _ _ _ _ _ cell_generated (cell_vc_valid k)

theorem cell_identity_correct (k : KAssignment) :
    ∃ value, Eval cellSignature [] none cellIdentity value ∧
      cellIdentityTy.denote cellSignature (cellSignature.datatypeModel k) k [] [] value := by
  have accepted : cellSignature.validate = .ok () := by compute_frk
  have adequate := cellSignature.datatypeModel_adequate k accepted
  refine ⟨.closure "c" (.var "c") [] none, .lam, ?_⟩
  simp only [cellIdentityTy, Ty.denote]
  refine ⟨True.intro, ?_⟩
  intro arg argTyped
  obtain ⟨n, measured⟩ := measure_total cellSignature (cellSignature.datatypeModel k) k
    accepted adequate [] [] "payload" ⟨"payload", "Cell", [⟨"cell", .field 0⟩]⟩ [] arg rfl
    (by simpa only [cellTy, Ty.denote, List.map_nil] using argTyped)
  refine ⟨arg, .closure (.var rfl), ?_⟩
  refine ⟨?_, .int n, .measure (.var ?_) measured, .measure (.var ?_) measured⟩
  · simpa only [cellTy, Ty.denote, List.map_nil] using argTyped
  · rfl
  · rfl

theorem cell_domain_inhabited (k : KAssignment) :
    cellTy.denote cellSignature (cellSignature.datatypeModel k) k [] [] (.ctor "cell" [.int 7]) := by
  have accepted : cellSignature.validate = .ok () := by compute_frk
  have adequate := cellSignature.datatypeModel_adequate k accepted
  apply (adequate [] [] "Cell" [] (.ctor "cell" [.int 7])).mpr
  refine ⟨⟨"Cell", 0, [⟨"cell", [.int]⟩]⟩, ⟨"cell", [.int]⟩, [.int 7],
    rfl, rfl, by simp, rfl, ?_⟩
  apply All₂.cons
  · simp [Ty.instantiateParams, Ty.freshenBinders, Ty.freshenBindersAux,
      Ty.denote, LSort.contains]
  · exact .nil

-- The added guard is inhabited; malformed runtime values cannot supply it.
theorem cell_guard_inhabited (k : KAssignment) :
    ∀ atom ∈ typeFacts cellSignature cellTy (.var "c"),
      atom.denote cellSignature k [("c", .ctor "cell" [.int 7])] := by
  have valid : cellSignature.validate = .ok () := by compute_frk
  exact typeFacts_hold valid (cellSignature.datatypeModel_adequate k valid)
    (cell_domain_inhabited k) (.var rfl)

theorem cell_guard_rejects_integer (k : KAssignment) :
    ¬ (∀ atom ∈ typeFacts cellSignature cellTy (.var "c"),
      atom.denote cellSignature k [("c", .int 0)]) := by
  intro holds
  have member : Atom.theory (.eq (.measure "payload" (.var "c"))
      (.measure "payload" (.var "c"))) ∈ typeFacts cellSignature cellTy (.var "c") := by
    compute_frk
    exact .head _
  obtain ⟨_, observed, _⟩ := holds _ member
  cases observed with
  | measure arg measured =>
    have known : LogicalEval cellSignature [("c", .int 0)] (.var "c") (.int 0) := .var rfl
    cases arg.deterministic known
    cases measured

-- Expected input refinements remain available inside annotated lambda bodies.
def nonnegative : Ty := .refine .int (.theory (.le (.int 0) (.var valueName)))
def positiveIdentity : Expr := .lam "x" .int (.var "x")
def positiveIdentityTy : Ty := .arrow "input" nonnegative nonnegative
def positiveVC : Cstr := actualVC {} positiveIdentity positiveIdentityTy

theorem positive_generated : generate {} positiveIdentity positiveIdentityTy = .ok positiveVC := by
  compute_frk

theorem positive_vc_valid (k : KAssignment) : positiveVC.Valid {} k := by
  unfold positiveVC
  reduce_actual_vc
  simp only [Cstr.Valid, Cstr.denote, Atom.denote, Formula.denote]
  intro env x _ positive result _ positiveResult _
  exact positiveResult

theorem positive_certified (k : KAssignment) :
    ∃ value, Eval {} [] none positiveIdentity value ∧
      positiveIdentityTy.denote {} (({} : Signature).datatypeModel k) k [] [] value :=
  generated_total_correctness _ _ _ _ _ positive_generated (positive_vc_valid k)

example : generate {} (.lam "x" .bool (.var "x")) (.arrow "x" .int .int) =
    .error "source and expected type have different shapes" := by compute_frk

-- A stronger annotation still generates its compatibility obligation.
def narrowAnnotationVC : Cstr :=
  .conj (.all "$g0" .int (.head (.theory (.le (.int 0) (.var "$g0")))))
    (.all "x" .int .truth)
theorem narrow_annotation_generated : generate {} (.lam "x" nonnegative (.var "x"))
    (.arrow "x" .int .int) = .ok narrowAnnotationVC := by compute_frk

theorem narrow_annotation_invalid (k : KAssignment) : ¬ narrowAnnotationVC.Valid {} k := by
  intro valid
  have h := (valid []).1 (.int (-1)) ⟨-1, rfl⟩
  obtain ⟨a, b, ha, hb, le⟩ := h
  cases ha
  cases hb with
  | var lookup =>
    have eq : b = -1 := by simpa [Environment.bind] using lookup.symm
    subst b
    contradiction

-- Definedness/input guards cannot certify a wrong result on an inhabited domain.
theorem negative_result_uncertifiable (k : KAssignment) (constraint : Cstr)
    (generated : generate {} (.lam "x" .int (.int (-1))) positiveIdentityTy = .ok constraint) :
    ¬ constraint.Valid {} k := by
  intro valid
  obtain ⟨fn, evaluated, typed⟩ := generated_total_correctness _ _ _ _ _ generated valid
  cases evaluated
  have argument : nonnegative.denote {} (({} : Signature).datatypeModel k) k [] [] (.int 0) := by
    simp only [nonnegative, Ty.denote, Atom.denote, Formula.denote, LSort.contains]
    exact ⟨⟨0, rfl⟩, 0, 0, .int, .var rfl, Int.le_refl 0⟩
  simp only [positiveIdentityTy, Ty.denote] at typed
  obtain ⟨result, applied, resultTyped⟩ := typed.2 (.int 0) argument
  cases applied with
  | closure evaluation =>
    cases evaluation
    simp only [nonnegative, Ty.denote, Atom.denote, Formula.denote] at resultTyped
    obtain ⟨_, a, b, ha, hb, le⟩ := resultTyped
    cases ha
    cases hb with
    | var lookup =>
      have eq : b = -1 := by simpa [Environment.bind] using lookup.symm
      subst b
      contradiction

-- An empty domain still requires a genuine function value.
def emptyDomain : Ty := .refine .int (.theory .falsity)
theorem empty_arrow_rejects_integer (s : Signature) (m : DataModel) (k : KAssignment)
    (types : TypeEnvironment) (env : Environment) (result : Ty) (n : Int) :
    ¬ (Ty.arrow "x" emptyDomain result).denote s m k types env (.int n) := by
  simp [Ty.denote, Value.IsFunction]

theorem empty_arrow_accepts_closure (s : Signature) (m : DataModel) (k : KAssignment)
    (types : TypeEnvironment) (env : Environment) :
    (Ty.arrow "x" emptyDomain .int).denote s m k types env
      (.closure "x" (.int 0) [] none) := by
  simp [Ty.denote, Value.IsFunction, emptyDomain, Atom.denote, Formula.denote]

theorem integer_cannot_have_empty_arrow (s : Signature) (k : KAssignment)
    (valid : s.validate = .ok ()) (result : Ty) :
    ¬ HasType s (s.datatypeModel k) k {} [] (.int 0) (.arrow "x" emptyDomain result) := by
  intro typed
  obtain ⟨value, evaluated, functionTyped⟩ := fundamental_closed s (s.datatypeModel k) k
    valid (s.datatypeModel_adequate k valid) _ _ typed
  cases evaluated
  exact empty_arrow_rejects_integer s _ k [] [] result 0 functionTyped

-- Full formation, not just scope, is an invariant of every typing rule.
theorem unformed_results_untypable (s : Signature) (m : DataModel) (k : KAssignment)
    (ctx : Context) (assumptions : List Atom) (expression : Expr) (type : Ty)
    (unformed : wfTy s ctx 512 type ≠ .ok ()) :
    ¬ HasType s m k ctx assumptions expression type :=
  fun typed => unformed typed.wellFormed

def unboundResult : Ty := .arrow "x" emptyDomain (.var 7)
example (m : DataModel) (k : KAssignment) (e : Expr) :
    ¬ HasType {} m k {} [] e unboundResult := by
  apply unformed_results_untypable
  compute_frk
  intro impossible
  cases impossible

-- Abstract equality is checked before instantiation; alpha and a concrete
-- datatype cannot be compared as though they were the same logical type.
def abstractComparison : Formula := .eq (.var valueName) (.ctor "box" [.int 0])
def unstableBody : Ty := .arrow "x" (.var 0)
  (.refine (.var 0) (.theory (.or abstractComparison (.not abstractComparison))))
def unstableIdentity : Expr := .tyApp
  (.ann polyId (.all unstableBody)) .int

example : wfTy boxSignature {} 512 (.all unstableBody) =
    .error "equality compares incompatible abstract types" := by compute_frk

example : generate boxSignature unstableIdentity (.arrow "x" .int .int) =
    .error "equality compares incompatible abstract types" := by compute_frk

-- Comparing an abstract value with itself remains available to polymorphic identity.
def refinedIdentityType : Ty := .all (.arrow "x" (.var 0)
  (.refine (.var 0) (.theory (.eq (.var valueName) (.var "x")))))
example : wfTy {} {} 512 refinedIdentityType = .ok () := by compute_frk
example : wfTy {} {} 512 (Ty.substType .int 0
    (.arrow "x" (.var 0) (.refine (.var 0)
      (.theory (.eq (.var valueName) (.var "x")))))) = .ok () := by compute_frk

theorem universal_rejects_integer (s : Signature) (m : DataModel) (k : KAssignment)
    (types : TypeEnvironment) (env : Environment) (body : Ty) :
    ¬ (Ty.all body).denote s m k types env (.int 0) := by
  intro typed
  simp only [Ty.denote] at typed
  obtain ⟨result, applied, _⟩ := typed (fun _ => False)
  cases applied

theorem adequate_datatype_rejects_integer (s : Signature) (m : DataModel) (k : KAssignment)
    (adequate : DatatypeAdequate s m k) (types : TypeEnvironment) (env : Environment)
    (name : String) (args : List Ty) :
    ¬ (Ty.data name args).denote s m k types env (.int 0) := by
  intro typed
  obtain ⟨_, _, _, _, _, _, impossible, _⟩ := (adequate types env name args (.int 0)).mp typed
  cases impossible

open Lean Elab in
run_elab do
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if (`SystemFRK.Adversarial).isPrefixOf name then
      if let .thmInfo _ := info then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "audit counterexample uses an unexpected axiom: {name}: {axiomName}"
        count := count + 1
  logInfo m!"Adversarial audit: {count} theorems checked; only standard Lean axioms"

end SystemFRK.Adversarial

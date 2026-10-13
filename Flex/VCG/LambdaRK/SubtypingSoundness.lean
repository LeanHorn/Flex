import Flex.VCG.LambdaRK.ConstraintLemmas
import Flex.VCG.LambdaRK.SyntaxEqualityLemmas

/-! Soundness of structural subtyping and its generated refinement clauses. -/
namespace LambdaRK

private def chosenName (avoid : List String) (state : Nat) : String :=
  if (valueName :: avoid).contains s!"$g{state}" then
    freshTermName s!"$g{state}" (valueName :: avoid) else s!"$g{state}"

private theorem chosenName_fresh (avoid : List String) (state : Nat) :
    chosenName avoid state ∉ valueName :: avoid := by
  unfold chosenName
  split
  · exact freshTermName_not_mem _ _
  · simpa using ‹¬ (valueName :: avoid).contains s!"$g{state}" = true›

private theorem freshAvoid_eq (avoid : List String) :
    freshAvoid avoid = fun state => .ok (chosenName avoid state, state+1) := rfl

theorem Ty.outerBase_names (type : Ty) (name : String)
    (member : name ∈ type.outerBase.allTermNames) : name ∈ type.allTermNames := by
  induction type using Ty.rec (motive_2 := fun _ => True) with
  | refine base p ih =>
    simpa only [Ty.allTermNames] using (List.mem_append_left p.freeVars (ih member))
  | nil | cons => trivial
  | _ => exact member

theorem Ty.outerPredicate_names (type : Ty) (atom : Atom) (name : String)
    (predicate : atom ∈ type.outerPredicates) (member : name ∈ atom.freeVars) :
    name ∈ type.allTermNames := by
  induction type using Ty.rec (motive_2 := fun _ => True) with
  | refine base p ih =>
    simp only [Ty.outerPredicates, List.mem_append, List.mem_singleton] at predicate
    rcases predicate with hp | rfl
    · simpa only [Ty.allTermNames] using (List.mem_append_left p.freeVars (ih hp))
    · simpa only [Ty.allTermNames] using (List.mem_append_right base.allTermNames member)
  | nil | cons => trivial
  | _ => simp [Ty.outerPredicates] at predicate

theorem Ty.bind_fresh (type : Ty) (fresh : name ∉ type.freeVars) :
    type.denote signature model assignment types (environment.bind name value) =
      type.denote signature model assignment types environment := by
  apply type.environment_congr
  intro n hn
  have different : n ≠ name := fun eq => fresh (eq ▸ hn)
  simp [Environment.bind, List.lookup_cons, show (n == name) = false from by simpa using different]

private theorem witness_predicate {environment : Environment} {value : Value} (predicate : Atom)
    (fresh : name ∉ predicate.freeVars) :
    (predicate.substTerm valueName (.var name)).denote signature assignment (environment.bind name value) ↔
      predicate.denote signature assignment (environment.bind valueName value) := by
  rw [atom_substitution signature assignment (environment.bind name value)
    valueName (.var name) predicate value (.var (by simp [Environment.bind]))]
  apply predicate.environment_congr
  intro n hn
  by_cases reserved : n = valueName
  · subst n; simp [Environment.bind]
  · have different : n ≠ name := fun eq => fresh (eq ▸ hn)
    simp [Environment.bind, List.lookup_cons,
      show (n == valueName) = false from by simpa using reserved,
      show (n == name) = false from by simpa using different]

private theorem substituted_codomain (body : Ty)
    {environment : Environment} {value : Value}
    (fresh : name ∉ body.freeVars) (reserved : name ≠ valueName) :
    (Ty.substTerm binder (.var name) body).denote signature model assignment types
        (environment.bind name value) =
      body.denote signature model assignment types (environment.bind binder value) := by
  rw [body.substTerm_denote signature model assignment types (environment.bind name value)
    binder (.var name) value (by simpa [LTerm.freeVars] using Ne.symm reserved)
    (.var (by simp [Environment.bind]))]
  apply body.environment_congr
  intro n hn
  by_cases same : n = binder
  · subst n; simp [Environment.bind]
  · have different : n ≠ name := fun eq => fresh (eq ▸ hn)
    simp [Environment.bind, List.lookup_cons,
      show (n == binder) = false from by simpa using same,
      show (n == name) = false from by simpa using different]

/-- A fresh refinement witness turns a generated Horn implication into the
semantic implication between the original outer refinements. -/
private theorem finishSubtype_sound
    (source target : Ty) (structural result : Cstr) (state finalState : Nat)
    (generated : (finishSubtype source target structural).run state = .ok (result, finalState))
    (satisfied : result.denote signature assignment environment)
    (structuralSound : structural.denote signature assignment environment →
      source.outerBase.denote signature model assignment types environment value →
      target.outerBase.denote signature model assignment types environment value)
    (typed : source.denote signature model assignment types environment value) :
    target.denote signature model assignment types environment value := by
  have ⟨base, predicates⟩ := source.denote_outer.mp typed
  apply target.denote_outer.mpr
  unfold finishSubtype at generated
  split at generated
  · simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at generated
    obtain ⟨rfl, rfl⟩ := generated
    refine ⟨structuralSound satisfied base, ?_⟩
    have empty := List.isEmpty_iff.mp ‹target.outerPredicates.isEmpty = true›
    simp [empty]
  · simp only [StateT.run, bind, StateT.bind, freshAvoid_eq, Except.bind, pure, StateT.pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at generated
    obtain ⟨rfl, rfl⟩ := generated
    obtain ⟨structureH, refines⟩ := (Cstr.andThen_denote _ _).mp satisfied
    refine ⟨structuralSound structureH base, ?_⟩
    let witness := chosenName (source.allTermNames ++ target.allTermNames) state
    have freshSource : witness ∉ source.allTermNames := fun h =>
      chosenName_fresh (source.allTermNames ++ target.allTermNames) state
        (List.mem_cons_of_mem _ (List.mem_append_left target.allTermNames h))
    have freshTarget : witness ∉ target.allTermNames := fun h =>
      chosenName_fresh (source.allTermNames ++ target.allTermNames) state
        (List.mem_cons_of_mem _ (List.mem_append_right source.allTermNames h))
    have clauses := refines value (source.denote_sort typed)
    have goals := (guardPredicates_denote _ _).mp clauses (by
      intro p hp
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp hp
      apply (witness_predicate original (fun h => freshSource (source.outerPredicate_names original witness originalMember h))).mpr
      exact predicates original originalMember)
    have heads : ∀ p ∈ target.outerPredicates,
        (p.substTerm valueName (.var witness)).denote signature assignment (environment.bind witness value) := by
      have all := (Cstr.heads_denote (target.outerPredicates.map (Atom.substTerm valueName (.var witness)))).mp
        (by simpa only [List.map_map, Function.comp_def, witness] using goals)
      intro p hp
      exact all _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    intro p hp
    exact (witness_predicate p (fun h => freshTarget (target.outerPredicate_names p witness hp h))).mp (heads p hp)

private theorem bind_generated {α β : Type} (first : GenM α) (next : α → GenM β)
    (state finalState : Nat) (result : β)
    (generated : (first >>= next).run state = .ok (result, finalState)) :
    ∃ value middle, first.run state = .ok (value, middle) ∧
      (next value).run middle = .ok (result, finalState) := by
  change (Except.bind (first state) (fun (value, middle) => next value middle)) = .ok (result, finalState) at generated
  cases run : first state with
  | error message => simp [run, Except.bind] at generated
  | ok pair => exact ⟨pair.1, pair.2, run, by simpa only [run, Except.bind, StateT.run] using generated⟩

/-- Every successful subtype check is a semantic implication whenever its
actual generated constraint holds in the current environment. This stronger
local statement composes under Horn guards and quantifiers. -/
theorem subtype_sound
    (signature : Signature) (context : Context) (fuel : Nat)
    (source target : Ty) (state finalState : Nat) (constraint : Cstr)
    (generated : (subtype signature context fuel source target).run state = .ok (constraint, finalState))
    (model : DataModel) (assignment : KAssignment) (types : TypeEnvironment)
    (environment : Environment) (value : Value)
    (satisfied : constraint.denote signature assignment environment)
    (typed : source.denote signature model assignment types environment value) :
    target.denote signature model assignment types environment value := by
  induction fuel generalizing context source target state finalState constraint types environment value with
  | zero => contradiction
  | succ fuel ih =>
    simp only [subtype] at generated
    split at generated
    · rename_i bs bt sourceEq targetEq
      exact finishSubtype_sound source target .truth constraint state finalState generated satisfied
        (fun _ h => by simpa only [sourceEq, targetEq] using h) typed
    · rename_i bs bt sourceEq targetEq
      exact finishSubtype_sound source target .truth constraint state finalState generated satisfied
        (fun _ h => by simpa only [sourceEq, targetEq] using h) typed
    · rename_i bs bt i j sourceEq targetEq
      by_cases equal : i = j
      · subst j
        simp only [beq_self_eq_true, failUnless, ↓reduceIte] at generated
        exact finishSubtype_sound source target .truth constraint state finalState generated satisfied
          (fun _ h => by simpa only [sourceEq, targetEq] using h) typed
      · simp [failUnless, equal, StateT.run, bind, StateT.bind, liftM, monadLift,
          Except.bind, pure, StateT.pure, Except.pure] at generated
        contradiction
    · rename_i bs bt a args b args' sourceEq targetEq
      by_cases equal : a = b ∧ args = args'
      · obtain ⟨rfl,rfl⟩ := equal
        simp only [beq_self_eq_true, Bool.and_self, failUnless, ↓reduceIte] at generated
        exact finishSubtype_sound source target .truth constraint state finalState generated satisfied
          (fun _ h => by simpa only [sourceEq, targetEq] using h) typed
      · simp [failUnless, equal, StateT.run, bind, StateT.bind, liftM, monadLift,
          Except.bind, pure, StateT.pure, Except.pure] at generated
        contradiction
    · rename_i bs bt x a b y a' b' sourceEq targetEq
      obtain ⟨pre, middle, preGenerated, rest⟩ := bind_generated _ _ _ _ _ generated
      obtain ⟨name, postState, freshGenerated, rest'⟩ := bind_generated _ _ _ _ _ rest
      simp only [freshAvoid_eq, StateT.run, Except.ok.injEq, Prod.mk.injEq] at freshGenerated
      obtain ⟨rfl, rfl⟩ := freshGenerated
      obtain ⟨post, endState, postGenerated, finish⟩ := bind_generated _ _ _ _ _ rest'
      apply finishSubtype_sound source target _ constraint endState finalState finish satisfied ?_ typed
      intro structuralH base
      rw [sourceEq] at base
      rw [targetEq]
      simp only [Ty.denote] at base ⊢
      intro argument argTyped
      obtain ⟨preH, postH⟩ := (Cstr.andThen_denote _ _).mp structuralH
      have sourceArgument := ih context a' a state middle pre preGenerated types environment argument preH argTyped
      obtain ⟨result, application, resultTyped⟩ := base argument sourceArgument
      refine ⟨result, application, ?_⟩
      let name := chosenName (source.allTermNames ++ target.allTermNames) middle
      have freshAll := chosenName_fresh (source.allTermNames ++ target.allTermNames) middle
      have reserved : name ≠ valueName := fun eq => freshAll (List.mem_cons.mpr (Or.inl eq))
      have sourceFresh : name ∉ source.outerBase.allTermNames := fun h =>
        freshAll (List.mem_cons_of_mem _ (List.mem_append_left _ (source.outerBase_names name h)))
      have targetFresh : name ∉ target.outerBase.allTermNames := fun h =>
        freshAll (List.mem_cons_of_mem _ (List.mem_append_right _ (target.outerBase_names name h)))
      rw [sourceEq, Ty.allTermNames] at sourceFresh
      rw [targetEq, Ty.allTermNames] at targetFresh
      have freshB : name ∉ b.freeVars := fun h =>
        sourceFresh (by simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inr (b.freeVars_mem_allTermNames name h)))
      have freshB' : name ∉ b'.freeVars := fun h =>
        targetFresh (by simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inr (b'.freeVars_mem_allTermNames name h)))
      have freshDomain : name ∉ a'.allTermNames := fun h =>
        targetFresh (by simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inl h))
      have postClauses := postH argument (a'.denote_sort argTyped)
      have postSatisfied := (guardPredicates_denote _ _).mp postClauses (by
        intro p hp
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp hp
        apply (witness_predicate original (fun h => freshDomain (a'.outerPredicate_names original name originalMember h))).mpr
        exact (a'.denote_outer.mp argTyped).2 original originalMember)
      have postTyped : (Ty.substTerm x (.var name) b).denote signature model assignment types
          (environment.bind name argument) result := by
        rw [substituted_codomain b freshB reserved]
        exact resultTyped
      have solved := ih _ _ _ (middle+1) endState post postGenerated types
        (environment.bind name argument) result postSatisfied postTyped
      rwa [substituted_codomain b' freshB' reserved] at solved
    · rename_i bs bt body body' sourceEq targetEq
      obtain ⟨structural, middle, subGenerated, finish⟩ := bind_generated _ _ _ _ _ generated
      apply finishSubtype_sound source target structural constraint middle finalState finish satisfied ?_ typed
      intro structuralH base
      rw [sourceEq] at base
      rw [targetEq]
      simp only [Ty.denote] at base ⊢
      intro candidate
      obtain ⟨result, app, bodyH⟩ := base candidate
      exact ⟨result, app, ih context.underType body body' state middle structural subGenerated
        (candidate :: types) environment result structuralH bodyH⟩
    · contradiction

/-- The local subtype theorem packaged for the declarative subsumption rule. -/
theorem subtype_entails
    (generated : (subtype signature context fuel source target).run state = .ok (constraint, finalState))
    (satisfied : Entails signature model assignment context assumptions constraint) :
    Subtype signature model assignment context assumptions source target := by
  intro types environment depth variables facts value typed
  exact subtype_sound signature context fuel source target state finalState constraint generated
    model assignment types environment value (satisfied types environment depth variables facts) typed

/-- Eliminating only outer refinements is always semantically valid. -/
theorem Subtype.outerBase (source : Ty) :
    Subtype signature model assignment context assumptions source source.outerBase := by
  intro types environment _ _ _ value typed
  exact (source.denote_outer.mp typed).1

end LambdaRK

import Flex.VCG.SystemFRK.Binding.Alpha
import Flex.VCG.SystemFRK.Binding.TypeIndices

/-! Capture-avoiding substitution preserves semantic types. -/
namespace SystemFRK

theorem logical_list_substitution
    (signature : Signature) (environment : Environment)
    (name : String) (replacement : LTerm) (terms : List LTerm)
    (replacementValue : Value) (values : List Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    LogicalListEval signature environment (terms.map (·.substTerm name replacement)) values ↔
      LogicalListEval signature (environment.bind name replacementValue) terms values := by
  induction terms generalizing values with
  | nil => constructor <;> intro derivation <;> cases derivation <;> constructor
  | cons term terms ih =>
    constructor
    · intro derivation
      cases derivation with
      | cons head tail =>
        exact .cons ((LogicalEval.substitution _ _ _ _ _ _ _ h).mp head) ((ih _).mp tail)
    · intro derivation
      cases derivation with
      | cons head tail =>
        exact .cons ((LogicalEval.substitution _ _ _ _ _ _ _ h).mpr head) ((ih _).mpr tail)

theorem formula_substitution
    (signature : Signature) (environment : Environment)
    (name : String) (replacement : LTerm) (formula : Formula) (replacementValue : Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    (formula.substTerm name replacement).denote signature environment ↔
      formula.denote signature (environment.bind name replacementValue) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | eq left right =>
    simp only [Formula.substTerm, Formula.denote, LogicalEval.substitution _ _ _ _ _ _ _ h]
  | le left right =>
    simp only [Formula.substTerm, Formula.denote, LogicalEval.substitution _ _ _ _ _ _ _ h]
  | and left right ihLeft ihRight =>
    exact and_congr ihLeft ihRight
  | or left right ihLeft ihRight =>
    exact or_congr ihLeft ihRight
  | not body ih => exact not_congr ih

theorem atom_substitution
    (signature : Signature) (assignment : KAssignment) (environment : Environment)
    (name : String) (replacement : LTerm) (atom : Atom) (replacementValue : Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    (atom.substTerm name replacement).denote signature assignment environment ↔
      atom.denote signature assignment (environment.bind name replacementValue) := by
  cases atom with
  | theory formula => exact formula_substitution _ _ _ _ _ _ h
  | kvar predicate arguments =>
    simp only [Atom.substTerm, Atom.denote, logical_list_substitution _ _ _ _ _ _ _ h]

private theorem bind_commute (environment : Environment) (x y : String) (a b : Value)
    (h : x ≠ y) (name : String) :
    ((environment.bind x a).bind y b).lookup name =
      ((environment.bind y b).bind x a).lookup name := by
  by_cases hx : name = x <;> by_cases hy : name = y
  · exact False.elim (h (hx.symm.trans hy))
  · subst name; simp [Environment.bind, List.lookup_cons,
      show (x == y) = false from by simpa using h]
  · subst name; simp [Environment.bind, List.lookup_cons,
      show (y == x) = false from by simpa using Ne.symm h]
  · simp [Environment.bind, List.lookup_cons,
      show (name == x) = false from by simpa using hx,
      show (name == y) = false from by simpa using hy]

private theorem bind_shadow (environment : Environment) (x : String) (a b : Value)
    (name : String) :
    ((environment.bind x a).bind x b).lookup name = (environment.bind x b).lookup name := by
  by_cases h : name = x
  · subst name; simp [Environment.bind]
  · simp [Environment.bind, List.lookup_cons, show (name == x) = false from by simpa using h]

private theorem LogicalEval.bind_fresh (signature : Signature) (environment : Environment)
    (term : LTerm) (result : Value) (name : String) (value : Value)
    (fresh : name ∉ term.freeVars) (evaluation : LogicalEval signature environment term result) :
    LogicalEval signature (environment.bind name value) term result := by
  apply (LogicalEval.environment_congr signature environment (environment.bind name value) term result _).mp evaluation
  intro n hn
  have different : n ≠ name := fun h => fresh (h ▸ hn)
  simp [Environment.bind, List.lookup_cons, show (n == name) = false from by simpa using different]

theorem Ty.substTermRaw_denote (body : Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment)
    (name : String) (replacement : LTerm) (replacementValue : Value)
    (fresh : ∀ binder ∈ body.TermBinders, binder ∉ replacement.freeVars)
    (witnessFresh : valueName ∉ replacement.freeVars)
    (evaluates : LogicalEval signature environment replacement replacementValue) :
    (body.substTermRaw name replacement).denote signature model assignment types environment =
      body.denote signature model assignment types (environment.bind name replacementValue) := by
  induction body using Ty.rec
    (motive_2 := fun ts => ∀ types environment,
      (∀ binder ∈ ts.flatMap Ty.TermBinders, binder ∉ replacement.freeVars) →
      LogicalEval signature environment replacement replacementValue →
      (ts.map (·.substTermRaw name replacement)).map
        (Ty.denote signature model assignment types environment) =
        ts.map (Ty.denote signature model assignment types (environment.bind name replacementValue)))
    generalizing types environment with
  | var => simp [Ty.substTermRaw, Ty.denote]
  | int => simp [Ty.substTermRaw, Ty.denote]
  | bool => simp [Ty.substTermRaw, Ty.denote]
  | data n args ih =>
    simp only [Ty.substTermRaw, Ty.denote]
    exact congrArg (model.datatype n) (ih types environment (by simpa only [Ty.TermBinders] using fresh) evaluates)
  | all b ih =>
    simp only [Ty.TermBinders] at fresh
    simp only [Ty.substTermRaw, Ty.denote, ih _ environment fresh evaluates]
  | arrow x a b ia ib =>
    have domain := ia types environment (fun n hn => fresh n (by simp [Ty.TermBinders, hn])) evaluates
    have binderFresh := fresh x (by simp [Ty.TermBinders])
    have codomain (arg : Value) :
        (if x == name then b else b.substTermRaw name replacement).denote
          signature model assignment types (environment.bind x arg) =
        b.denote signature model assignment types ((environment.bind name replacementValue).bind x arg) := by
      by_cases same : x = name
      · subst x
        simp only [beq_self_eq_true, ite_true]
        exact b.environment_congr signature model assignment types _ _
          (fun n _ => (bind_shadow environment name replacementValue arg n).symm)
      · simp only [show (x == name) = false from by simpa using same, Bool.false_eq_true, ite_false]
        rw [ib types (environment.bind x arg)
          (fun n hn => fresh n (by simp [Ty.TermBinders, hn]))
          (LogicalEval.bind_fresh signature environment replacement replacementValue x arg binderFresh evaluates)]
        exact b.environment_congr signature model assignment types _ _
          (fun n _ => bind_commute environment x name arg replacementValue same n)
    simp only [Ty.substTermRaw, Ty.denote, domain, codomain]
  | refine b pred ih =>
    simp only [Ty.TermBinders] at fresh
    have base := ih types environment fresh evaluates
    have predicate (v : Value) :
        (if name == valueName then pred else pred.substTerm name replacement).denote
          signature assignment (environment.bind valueName v) ↔
        pred.denote signature assignment ((environment.bind name replacementValue).bind valueName v) := by
      by_cases same : name = valueName
      · subst name
        simp only [beq_self_eq_true, ite_true]
        exact pred.environment_congr signature assignment _ _
          (fun n _ => (bind_shadow environment valueName replacementValue v n).symm)
      · simp only [show (name == valueName) = false from by simpa using same, Bool.false_eq_true, ite_false]
        rw [atom_substitution signature assignment _ name replacement pred replacementValue
          (LogicalEval.bind_fresh signature environment replacement replacementValue valueName v witnessFresh evaluates)]
        exact pred.environment_congr signature assignment _ _
          (fun n _ => bind_commute environment valueName name v replacementValue (Ne.symm same) n)
    funext v
    simp only [Ty.substTermRaw, Ty.denote, base]
    exact propext (and_congr Iff.rfl (predicate v))
  | nil => rfl
  | cons a as ia ib =>
    rename_i types environment fresh evaluates
    simp only [List.map_cons]
    rw [ia types environment (fun n hn => fresh n (by simp [hn])) evaluates,
      ib types environment (fun n hn => fresh n (by simp [hn])) evaluates]

theorem Ty.substTerm_denote (body : Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment)
    (name : String) (replacement : LTerm) (replacementValue : Value)
    (witnessFresh : valueName ∉ replacement.freeVars)
    (evaluates : LogicalEval signature environment replacement replacementValue) :
    (Ty.substTerm name replacement body).denote signature model assignment types environment =
      body.denote signature model assignment types (environment.bind name replacementValue) := by
  unfold Ty.substTerm
  rw [Ty.substTermRaw_denote _ signature model assignment types environment name replacement replacementValue
    (fun n hn => body.freshenBinders_avoids replacement.freeVars n hn) witnessFresh evaluates,
    body.freshenBinders_denote]

theorem Ty.freeVars_mem_allTermNames (type : Ty) (name : String)
    (member : name ∈ type.freeVars) : name ∈ type.allTermNames := by
  induction type using Ty.rec
    (motive_2 := fun ts => name ∈ ts.flatMap Ty.freeVars → name ∈ ts.flatMap Ty.allTermNames) with
  | var | int | bool => simp [Ty.freeVars] at member
  | data n args ih => simpa only [Ty.allTermNames] using ih (by simpa only [Ty.freeVars] using member)
  | all b ih => simpa only [Ty.allTermNames] using ih (by simpa only [Ty.freeVars] using member)
  | arrow x a b ia ib =>
    simp only [Ty.freeVars, List.mem_append, List.mem_filter, bne_iff_ne] at member
    simp only [Ty.allTermNames, List.mem_cons, List.mem_append]
    rcases member with h | ⟨h, _⟩
    · exact Or.inr (Or.inl (ia h))
    · exact Or.inr (Or.inr (ib h))
  | refine a p ih =>
    simp only [Ty.freeVars, List.mem_append, List.mem_filter, bne_iff_ne] at member
    simp only [Ty.allTermNames, List.mem_append]
    rcases member with h | ⟨h, _⟩
    · exact Or.inl (ih h)
    · exact Or.inr h
  | nil => simp_all
  | cons a as ia ib =>
    rename_i member
    simp only [List.flatMap_cons, List.mem_append] at member ⊢
    exact member.elim (fun h => Or.inl (ia h)) (fun h => Or.inr (ib h))

/-- Simultaneous type substitution preserves meaning under binders and protected free names. -/
theorem Ty.mapTypes_denote (body : Ty) (f : Nat → Nat → Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (crossed : Nat) (source target : TypeEnvironment) (original environment : Environment)
    (protectedNames : List String)
    (fresh : ∀ binder ∈ body.TermBinders, binder ∉ protectedNames)
    (agree : ∀ name ∈ protectedNames, environment.lookup name = original.lookup name)
    (indices : ∀ (boundTypes : TypeEnvironment) (env : Environment),
      (∀ name ∈ protectedNames, env.lookup name = original.lookup name) → ∀ i,
      (f (crossed + boundTypes.length) i).denote signature model assignment
          (boundTypes ++ target) env =
        (boundTypes ++ source)[i]?.getD (fun _ => False)) :
    (body.mapTypes f crossed).denote signature model assignment target environment =
      body.denote signature model assignment source environment := by
  induction body using Ty.rec
    (motive_2 := fun ts => ∀ crossed source target environment,
      (∀ binder ∈ ts.flatMap Ty.TermBinders, binder ∉ protectedNames) →
      (∀ name ∈ protectedNames, environment.lookup name = original.lookup name) →
      (∀ (boundTypes : TypeEnvironment) (env : Environment),
        (∀ name ∈ protectedNames, env.lookup name = original.lookup name) → ∀ i,
        (f (crossed + boundTypes.length) i).denote signature model assignment
          (boundTypes ++ target) env =
          (boundTypes ++ source)[i]?.getD (fun _ => False)) →
      (ts.map (·.mapTypes f crossed)).map (Ty.denote signature model assignment target environment) =
        ts.map (Ty.denote signature model assignment source environment))
    generalizing crossed source target environment with
  | var i => simpa [Ty.mapTypes, Ty.denote] using indices [] environment agree i
  | int => simp [Ty.mapTypes, Ty.denote]
  | bool => simp [Ty.mapTypes, Ty.denote]
  | data n args ih =>
    simp only [Ty.mapTypes, Ty.denote]
    exact congrArg (model.datatype n) (ih crossed source target environment
      (by simpa only [Ty.TermBinders] using fresh) agree indices)
  | arrow x a b ia ib =>
    have dom := ia crossed source target environment
      (fun n hn => fresh n (by simp [Ty.TermBinders, hn])) agree indices
    have cod (v : Value) := ib crossed source target (environment.bind x v)
      (fun n hn => fresh n (by simp [Ty.TermBinders, hn])) (by
        intro n hn
        have different : n ≠ x := fun h => fresh x (by simp [Ty.TermBinders]) (h ▸ hn)
        simpa [Environment.bind, List.lookup_cons,
          show (n == x) = false from by simpa using different] using agree n hn) indices
    simp only [Ty.mapTypes, Ty.denote, dom, cod]
  | all b ih =>
    simp only [Ty.TermBinders] at fresh
    have next (candidate : Candidate) := ih (crossed + 1) (candidate :: source)
      (candidate :: target) environment fresh agree (by
        intro boundTypes env agreed i
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          indices (boundTypes ++ [candidate]) env agreed i)
    simp only [Ty.mapTypes, Ty.denote, next]
  | refine b p ih =>
    simp only [Ty.TermBinders] at fresh
    simp only [Ty.mapTypes, Ty.denote, ih crossed source target environment fresh agree indices]
  | nil => rfl
  | cons a as ia ib =>
    rename_i crossed source target environment fresh agree indices
    simp only [List.map_cons]
    rw [ia crossed source target environment (fun n hn => fresh n (by simp [hn])) agree indices,
      ib crossed source target environment (fun n hn => fresh n (by simp [hn])) agree indices]

theorem Ty.substType_denote (body replacement : Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) :
    (Ty.substType replacement 0 body).denote signature model assignment types environment =
      body.denote signature model assignment
        (replacement.denote signature model assignment types environment :: types) environment := by
  let argument := replacement.freshenBinders body.allTermNames
  let freshBody := body.freshenBinders argument.allTermNames
  change (freshBody.mapTypes (fun d i =>
    if i == 0 + d then argument.shiftTypes d 0 else .var (if 0 + d < i then i - 1 else i)) 0).denote
    signature model assignment types environment = _
  have mapped := freshBody.mapTypes_denote
    (fun d i => if i == 0 + d then argument.shiftTypes d 0 else .var (if 0 + d < i then i - 1 else i))
    signature model assignment 0
    (argument.denote signature model assignment types environment :: types) types
    environment environment argument.allTermNames
    (fun n hn => body.freshenBinders_avoids argument.allTermNames n hn)
    (fun _ _ => rfl) (by
      intro boundTypes env agree i
      simp only [Nat.zero_add]
      by_cases same : i = boundTypes.length
      · subst i
        simp only [beq_self_eq_true, ite_true]
        rw [argument.shiftTypes_denote signature model assignment types boundTypes env,
          argument.environment_congr signature model assignment types env environment
            (fun n hn => agree n (argument.freeVars_mem_allTermNames n hn)),
          List.getElem?_append_right (Nat.le_refl _)]
        simp
      · have different : (i == boundTypes.length) = false := by simpa using same
        simp only [different, Bool.false_eq_true, ite_false, Ty.denote]
        by_cases before : i < boundTypes.length
        · simp only [show ¬boundTypes.length < i from by omega, ite_false]
          rw [List.getElem?_append_left before, List.getElem?_append_left before]
        · have after : boundTypes.length < i := by omega
          simp only [after, ite_true]
          rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          have difference : i - boundTypes.length = (i - 1 - boundTypes.length) + 1 := by omega
          rw [difference]
          rfl)
  rw [mapped, body.freshenBinders_denote]
  have argumentEq := replacement.freshenBinders_denote signature model assignment types environment body.allTermNames
  change argument.denote signature model assignment types environment = _ at argumentEq
  rw [argumentEq]

theorem Ty.instantiateParams_denote (field : Ty) (arguments : List Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) :
    (Ty.instantiateParams arguments field).denote signature model assignment types environment =
      field.denote signature model assignment
        (arguments.map (Ty.denote signature model assignment types environment) ++ types) environment := by
  let args := arguments.map (·.freshenBinders field.allTermNames)
  let protectedNames := args.flatMap Ty.allTermNames
  let candidates := args.map (Ty.denote signature model assignment types environment)
  let freshField := field.freshenBinders protectedNames
  change (freshField.mapTypes (fun d i =>
    if i < d then .var i else match args[i - d]? with
      | some replacement => replacement.shiftTypes d 0
      | none => .var (i - args.length)) 0).denote
    signature model assignment types environment = _
  have mapped := freshField.mapTypes_denote
    (fun d i => if i < d then .var i else match args[i - d]? with
      | some replacement => replacement.shiftTypes d 0
      | none => .var (i - args.length))
    signature model assignment 0 (candidates ++ types) types environment environment protectedNames
    (fun n hn => field.freshenBinders_avoids protectedNames n hn)
    (fun _ _ => rfl) (by
      intro boundTypes env agree i
      simp only [Nat.zero_add]
      by_cases before : i < boundTypes.length
      · simp only [before, ite_true, Ty.denote]
        rw [List.getElem?_append_left before, List.getElem?_append_left before]
      · simp only [before, ite_false]
        rw [List.getElem?_append_right (by omega)]
        cases found : args[i - boundTypes.length]? with
        | some arg =>
          rw [arg.shiftTypes_denote signature model assignment types boundTypes env,
            arg.environment_congr signature model assignment types env environment (by
              intro n hn
              exact agree n (List.mem_flatMap.mpr ⟨arg, List.mem_of_getElem? found,
                arg.freeVars_mem_allTermNames n hn⟩))]
          have bound : i - boundTypes.length < candidates.length := by
            simpa [candidates] using List.getElem?_eq_some_iff.mp found |>.1
          rw [List.getElem?_append_left bound]
          simp [candidates, List.getElem?_map, found]
        | none =>
          simp only [Ty.denote]
          have bound := List.getElem?_eq_none_iff.mp found
          have length : candidates.length = args.length := by simp [candidates]
          rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          congr 2
          omega)
  rw [mapped, field.freshenBinders_denote]
  have candidateEq : candidates = arguments.map (Ty.denote signature model assignment types environment) := by
    simp only [candidates, args, List.map_map]
    apply List.map_congr_left
    intro arg _
    exact arg.freshenBinders_denote signature model assignment types environment field.allTermNames
  rw [candidateEq]

end SystemFRK

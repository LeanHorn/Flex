import Flex.VCG.LambdaRK.BindingLemmas
import Flex.VCG.LambdaRK.EnvironmentLemmas

/-! Capture avoidance for the named logical binders in types. -/
namespace LambdaRK

private theorem mem_le_foldl_max (xs : List Nat) (start n : Nat) (h : n ∈ xs) :
    n ≤ xs.foldl max start := by
  have accumulator (ys : List Nat) (k : Nat) : k ≤ ys.foldl max k := by
    induction ys generalizing k with
    | nil => simp_all
    | cons a as ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  induction xs generalizing start with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldl_cons]
    rcases h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (accumulator _ _)
    · exact ih _ h

theorem freshTermName_not_mem (base : String) (avoid : List String) :
    freshTermName base avoid ∉ avoid := by
  unfold freshTermName
  dsimp only
  split
  · rename_i name found
    have valid := List.find?_some found
    simpa using valid
  · intro member
    have bound := mem_le_foldl_max (avoid.map String.length) 0 _
      (List.mem_map.mpr ⟨_, member, rfl⟩)
    simp only [String.length_ofList, List.length_replicate] at bound
    omega

theorem Ty.freshenBindersAux_avoids (type : Ty) (avoid : List String)
    (renames : List (String × String)) (name : String)
    (bound : name ∈ (type.freshenBindersAux avoid renames).TermBinders) : name ∉ avoid := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ avoid renames name,
      name ∈ (ts.map (·.freshenBindersAux avoid renames)).flatMap Ty.TermBinders →
      name ∉ avoid)
    generalizing avoid renames name with
  | var => simp [Ty.freshenBindersAux, Ty.TermBinders] at bound
  | int => simp [Ty.freshenBindersAux, Ty.TermBinders] at bound
  | bool => simp [Ty.freshenBindersAux, Ty.TermBinders] at bound
  | data n args ih => exact ih avoid renames name (by simpa only [Ty.freshenBindersAux, Ty.TermBinders] using bound)
  | all body ih => exact ih avoid renames name (by simpa only [Ty.freshenBindersAux, Ty.TermBinders] using bound)
  | refine body pred ih => exact ih avoid renames name (by simpa only [Ty.freshenBindersAux, Ty.TermBinders] using bound)
  | arrow x a b ia ib =>
    let next := if avoid.contains x then
      freshTermName x (avoid ++ a.allTermNames ++ b.allTermNames) else x
    have fresh : next ∉ avoid := by
      dsimp [next]
      split
      · exact fun h => freshTermName_not_mem x (avoid ++ a.allTermNames ++ b.allTermNames) (List.mem_append_left _ (List.mem_append_left _ h))
      · simpa using ‹¬avoid.contains x = true›
    simp only [Ty.freshenBindersAux, Ty.TermBinders] at bound
    change name ∈ next :: _ at bound
    simp only [List.mem_cons, List.mem_append] at bound
    rcases bound with rfl | ha | hb
    · exact fresh
    · exact ia _ _ _ ha
    · exact fun h => ib _ _ _ hb (by simp [h])
  | nil => simp_all
  | cons a as ia ib =>
    rename_i avoid renames name bound
    simp only [List.map_cons, List.flatMap_cons, List.mem_append] at bound
    rcases bound with h | h
    · exact ia _ _ _ h
    · exact ib _ _ _ h

theorem Ty.freshenBinders_avoids (type : Ty) (avoid : List String) (name : String)
    (bound : name ∈ (type.freshenBinders avoid).TermBinders) : name ∉ avoid := by
  exact fun h => type.freshenBindersAux_avoids _ [] name bound (by simp [h])

abbrev renamed (renames : List (String × String)) (name : String) : String :=
  (renames.lookup name).getD name

@[simp] theorem renamed_nil (name : String) : renamed [] name = name := rfl
@[simp] theorem renamed_cons (renames : List (String × String)) (x y name : String) :
    renamed ((x,y) :: renames) name = if name = x then y else renamed renames name := by
  by_cases h : name = x <;> simp [renamed, List.lookup_cons, h, show (name == x) = decide (name = x) from rfl]

private theorem lookup_without_witness (renames : List (String × String)) (name : String)
    (different : name ≠ valueName) :
    (renames.filter (fun entry => entry.1 != valueName)).lookup name = renames.lookup name := by
  induction renames with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨x,y⟩
    by_cases hx : x = valueName
    · subst x; simp [List.lookup_cons, ih, show (name == valueName) = false from by simpa using different]
    · simp [hx, List.lookup_cons, ih]

private theorem renamed_without_witness (renames : List (String × String)) (name : String) :
    renamed (renames.filter (fun entry => entry.1 != valueName)) name =
      if name = valueName then valueName else renamed renames name := by
  by_cases h : name = valueName
  · subst name
    have hnone : (renames.filter (fun entry => entry.1 != valueName)).lookup valueName = none := by
      induction renames with
      | nil => rfl
      | cons entry rest ih =>
        rcases entry with ⟨x,y⟩
        by_cases hx : x = valueName
        · subst x; simp [ih]
        · have hy : valueName ≠ x := Ne.symm hx
          simp [hx, List.lookup_cons, ih, show (valueName == x) = false from by simpa using hy]
    simp [renamed, hnone]
  · simp [h, renamed, lookup_without_witness _ _ h]

private theorem renamed_ne_witness (renames : List (String × String)) (name : String)
    (targets : ∀ entry ∈ renames, entry.2 ≠ valueName) (h : name ≠ valueName) :
    renamed renames name ≠ valueName := by
  induction renames with
  | nil => exact h
  | cons entry rest ih =>
    rcases entry with ⟨x,y⟩
    simp only [renamed_cons]
    split
    · exact targets (x,y) (by simp)
    · exact ih (fun entry he => targets entry (by simp [he]))

theorem LogicalEval.renaming (signature : Signature) (left right : Environment)
    (renames : List (String × String)) (term : LTerm) (value : Value)
    (agree : ∀ name ∈ term.freeVars, left.lookup (renamed renames name) = right.lookup name) :
    LogicalEval signature left (term.renameNames renames) value ↔
      LogicalEval signature right term value := by
  induction term using LTerm.rec
    (motive_2 := fun terms => ∀ values,
      (∀ name ∈ terms.flatMap LTerm.freeVars,
        left.lookup (renamed renames name) = right.lookup name) →
      (LogicalListEval signature left (terms.map (·.renameNames renames)) values ↔
        LogicalListEval signature right terms values))
    generalizing value with
  | var name =>
    simp only [LTerm.renameNames, LogicalEval.var_iff]
    rw [agree name (by simp [LTerm.freeVars])]
  | int => simp only [LTerm.renameNames]; constructor <;> intro h <;> cases h <;> constructor
  | bool => simp only [LTerm.renameNames]; constructor <;> intro h <;> cases h <;> constructor
  | add a b ia ib =>
    simp only [LTerm.renameNames]
    have ha := ia (agree := fun n hn => agree n (by simp [LTerm.freeVars, hn]))
    have hb := ib (agree := fun n hn => agree n (by simp [LTerm.freeVars, hn]))
    constructor
    · intro h; cases h with | add a b => exact .add ((ha _).mp a) ((hb _).mp b)
    · intro h; cases h with | add a b => exact .add ((ha _).mpr a) ((hb _).mpr b)
  | ctor name fields ih =>
    simp only [LTerm.renameNames]
    simp only [LTerm.freeVars] at agree
    constructor
    · intro h; cases h with | ctor fields => exact .ctor ((ih _ agree).mp fields)
    · intro h; cases h with | ctor fields => exact .ctor ((ih _ agree).mpr fields)
  | measure name arg ih =>
    simp only [LTerm.renameNames]
    simp only [LTerm.freeVars] at agree
    constructor
    · intro h; cases h with | measure arg h => exact .measure ((ih _ agree).mp arg) h
    · intro h; cases h with | measure arg h => exact .measure ((ih _ agree).mpr arg) h
  | nil => constructor <;> intro h <;> cases h <;> constructor
  | cons t ts ih it =>
    rename_i values agree
    have ha := ih (agree := fun n hn => agree n (by simp [hn]))
    have hb := fun values => it values (fun n hn => agree n (by simp [hn]))
    constructor
    · intro h; cases h with | cons h t => exact .cons ((ha _).mp h) ((hb _).mp t)
    · intro h; cases h with | cons h t => exact .cons ((ha _).mpr h) ((hb _).mpr t)

theorem LogicalListEval.renaming (signature : Signature) (left right : Environment)
    (renames : List (String × String)) (terms : List LTerm) (values : List Value)
    (agree : ∀ name ∈ terms.flatMap LTerm.freeVars,
      left.lookup (renamed renames name) = right.lookup name) :
    LogicalListEval signature left (terms.map (·.renameNames renames)) values ↔
      LogicalListEval signature right terms values := by
  induction terms generalizing values with
  | nil => constructor <;> intro h <;> cases h <;> constructor
  | cons t ts ih =>
    have ha := LogicalEval.renaming signature left right renames t
      (agree := fun n hn => agree n (by simp [hn]))
    have hb := ih (agree := fun n hn => agree n (by simp [hn]))
    constructor
    · intro h; cases h with | cons h t => exact .cons ((ha _).mp h) ((hb _).mp t)
    · intro h; cases h with | cons h t => exact .cons ((ha _).mpr h) ((hb _).mpr t)

theorem Formula.renaming (signature : Signature) (left right : Environment)
    (renames : List (String × String)) (formula : Formula)
    (agree : ∀ name ∈ formula.freeVars, left.lookup (renamed renames name) = right.lookup name) :
    (formula.renameNames renames).denote signature left ↔ formula.denote signature right := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | eq a b | le a b =>
    have ha := LogicalEval.renaming signature left right renames a
      (agree := fun n hn => agree n (by simp [Formula.freeVars, hn]))
    have hb := LogicalEval.renaming signature left right renames b
      (agree := fun n hn => agree n (by simp [Formula.freeVars, hn]))
    simp only [Formula.renameNames, Formula.denote, ha, hb]
  | and a b ia ib =>
    exact and_congr (ia (fun n hn => agree n (by simp [Formula.freeVars, hn])))
      (ib (fun n hn => agree n (by simp [Formula.freeVars, hn])))
  | or a b ia ib =>
    exact or_congr (ia (fun n hn => agree n (by simp [Formula.freeVars, hn])))
      (ib (fun n hn => agree n (by simp [Formula.freeVars, hn])))
  | not a ih => exact not_congr (ih agree)

theorem Atom.renaming (signature : Signature) (assignment : KAssignment)
    (left right : Environment) (renames : List (String × String)) (atom : Atom)
    (agree : ∀ name ∈ atom.freeVars, left.lookup (renamed renames name) = right.lookup name) :
    (atom.renameNames renames).denote signature assignment left ↔
      atom.denote signature assignment right := by
  cases atom with
  | theory f => exact f.renaming signature left right renames agree
  | kvar name args =>
    simp only [Atom.renameNames, Atom.denote,
      LogicalListEval.renaming signature left right renames args _ agree]

private theorem next_fresh (avoid : List String) (x : String) (a b : Ty) :
    (if avoid.contains x then freshTermName x (avoid ++ a.allTermNames ++ b.allTermNames)
      else x) ∉ avoid := by
  split
  · exact fun h => freshTermName_not_mem x (avoid ++ a.allTermNames ++ b.allTermNames)
      (List.mem_append_left _ (List.mem_append_left _ h))
  · simpa using ‹¬avoid.contains x = true›

/-- Alpha-renaming is sound under environments related by the current name map.
The avoidance set contains the images of free names; the fixed refinement
witness is separately reserved because refinements bind it implicitly. -/
theorem Ty.freshenBindersAux_denote (type : Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (left right : Environment)
    (avoid : List String) (renames : List (String × String))
    (witness : valueName ∈ avoid)
    (targets : ∀ entry ∈ renames, entry.2 ≠ valueName)
    (covered : ∀ name ∈ type.freeVars, renamed renames name ∈ avoid)
    (agree : ∀ name ∈ type.freeVars,
      left.lookup (renamed renames name) = right.lookup name) :
    (type.freshenBindersAux avoid renames).denote signature model assignment types left =
      type.denote signature model assignment types right := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ types left right avoid renames,
      valueName ∈ avoid →
      (∀ entry ∈ renames, entry.2 ≠ valueName) →
      (∀ name ∈ ts.flatMap Ty.freeVars, renamed renames name ∈ avoid) →
      (∀ name ∈ ts.flatMap Ty.freeVars,
        left.lookup (renamed renames name) = right.lookup name) →
      (ts.map (·.freshenBindersAux avoid renames)).map
        (Ty.denote signature model assignment types left) =
        ts.map (Ty.denote signature model assignment types right))
    generalizing types left right avoid renames with
  | var => simp [Ty.freshenBindersAux, Ty.denote]
  | int => simp [Ty.freshenBindersAux, Ty.denote]
  | bool => simp [Ty.freshenBindersAux, Ty.denote]
  | data name args ih =>
    simp only [Ty.freeVars] at covered agree
    simp only [Ty.freshenBindersAux, Ty.denote]
    exact congrArg (model.datatype name) (ih types left right avoid renames witness targets covered agree)
  | all body ih =>
    simp only [Ty.freeVars] at covered agree
    simp only [Ty.freshenBindersAux, Ty.denote,
      ih _ left right avoid renames witness targets covered agree]
  | arrow x a b ia ib =>
    let next := if avoid.contains x then freshTermName x (avoid ++ a.allTermNames ++ b.allTermNames) else x
    have fresh : next ∉ avoid := next_fresh avoid x a b
    have nextWitness : next ≠ valueName := fun h => fresh (h ▸ witness)
    have dom := ia types left right avoid renames witness targets
      (fun n hn => covered n (by simp [Ty.freeVars, hn]))
      (fun n hn => agree n (by simp [Ty.freeVars, hn]))
    have cod (v : Value) := ib types (left.bind next v) (right.bind x v)
      (next :: avoid) ((x,next) :: renames) (by simp [witness])
      (by intro entry he; simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact nextWitness
          · exact targets entry he)
      (by
        intro n hn
        by_cases h : n = x
        · simp [renamed_cons, h]
        · simp only [renamed_cons, if_neg h, List.mem_cons]
          exact Or.inr (covered n (by simp [Ty.freeVars, hn, h])))
      (by
        intro n hn
        by_cases h : n = x
        · subst n; simp [renamed_cons, Environment.bind]
        · have mapped := covered n (by simp [Ty.freeVars, hn, h])
          have distinct : renamed renames n ≠ next := fun eq => fresh (eq ▸ mapped)
          simp only [renamed_cons, if_neg h, Environment.bind, List.lookup_cons]
          simp only [show (renamed renames n == next) = false from by simpa using distinct,
            show (n == x) = false from by simpa using h]
          exact agree n (by simp [Ty.freeVars, hn, h]))
    simp only [Ty.freshenBindersAux, Ty.denote]
    change (fun fn => ∀ arg, _ → ∃ result, Apply signature fn arg result ∧ _) = _
    rw [dom]
    funext fn
    apply propext
    constructor
    · intro h arg ha
      obtain ⟨result, eval, ty⟩ := h arg ha
      exact ⟨result, eval, (congrFun (cod arg) result) ▸ ty⟩
    · intro h arg ha
      obtain ⟨result, eval, ty⟩ := h arg ha
      exact ⟨result, eval, (congrFun (cod arg) result).symm ▸ ty⟩
  | refine base atom ih =>
    have baseEq := ih types left right avoid renames witness targets
      (fun n hn => covered n (by simp [Ty.freeVars, hn]))
      (fun n hn => agree n (by simp [Ty.freeVars, hn]))
    have predEq (v : Value) := atom.renaming signature assignment
      (left.bind valueName v) (right.bind valueName v)
      (renames.filter (fun entry => entry.1 != valueName)) (by
        intro n hn
        rw [renamed_without_witness]
        by_cases h : n = valueName
        · subst n; simp [Environment.bind]
        · have distinct := renamed_ne_witness renames n targets h
          simp only [if_neg h, Environment.bind, List.lookup_cons,
            show (renamed renames n == valueName) = false from by simpa using distinct,
            show (n == valueName) = false from by simpa using h]
          exact agree n (by simp [Ty.freeVars, hn, h]))
    funext v
    simp only [Ty.freshenBindersAux, Ty.denote, baseEq]
    exact propext (and_congr Iff.rfl (predEq v))
  | nil => rfl
  | cons a as ia ib =>
    rename_i types left right avoid renames witness targets covered agree
    simp only [List.map_cons]
    rw [ia types left right avoid renames witness targets
      (fun n hn => covered n (by simp [hn])) (fun n hn => agree n (by simp [hn])),
      ib types left right avoid renames witness targets
      (fun n hn => covered n (by simp [hn])) (fun n hn => agree n (by simp [hn]))]

theorem Ty.freshenBinders_denote (type : Ty)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) (avoid : List String) :
    (type.freshenBinders avoid).denote signature model assignment types environment =
      type.denote signature model assignment types environment := by
  apply type.freshenBindersAux_denote
  · simp
  · simp
  · intro n hn; simp [hn]
  · simp

theorem LTerm.renameNames_freeVars (term : LTerm) (renames : List (String × String)) :
    (term.renameNames renames).freeVars = term.freeVars.map (renamed renames) := by
  induction term using LTerm.rec
    (motive_2 := fun ts => (ts.map (·.renameNames renames)).flatMap LTerm.freeVars =
      (ts.flatMap LTerm.freeVars).map (renamed renames)) with
  | var => simp [LTerm.renameNames, LTerm.freeVars, renamed]
  | int => simp [LTerm.renameNames, LTerm.freeVars]
  | bool => simp [LTerm.renameNames, LTerm.freeVars]
  | add => simp_all [LTerm.renameNames, LTerm.freeVars, List.map_append]
  | ctor => simp_all [LTerm.renameNames, LTerm.freeVars]
  | measure => simp_all [LTerm.renameNames, LTerm.freeVars]
  | nil => rfl
  | cons => simp_all [List.map_append]

theorem Formula.renameNames_freeVars (formula : Formula) (renames : List (String × String)) :
    (formula.renameNames renames).freeVars = formula.freeVars.map (renamed renames) := by
  induction formula <;>
    simp_all [Formula.renameNames, Formula.freeVars, LTerm.renameNames_freeVars, List.map_append]

theorem Atom.renameNames_freeVars (atom : Atom) (renames : List (String × String)) :
    (atom.renameNames renames).freeVars = atom.freeVars.map (renamed renames) := by
  cases atom with
  | theory formula => exact formula.renameNames_freeVars renames
  | kvar name args =>
    simp only [Atom.renameNames, Atom.freeVars, List.flatMap_map,
      LTerm.renameNames_freeVars, List.map_flatMap]

theorem Ty.freshenBindersAux_freeVars (type : Ty)
    (avoid : List String) (renames : List (String × String))
    (witness : valueName ∈ avoid)
    (targets : ∀ entry ∈ renames, entry.2 ≠ valueName)
    (covered : ∀ name ∈ type.freeVars, renamed renames name ∈ avoid) (name : String) :
    name ∈ (type.freshenBindersAux avoid renames).freeVars ↔
      ∃ original ∈ type.freeVars, renamed renames original = name := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ avoid renames,
      valueName ∈ avoid →
      (∀ entry ∈ renames, entry.2 ≠ valueName) →
      (∀ name ∈ ts.flatMap Ty.freeVars, renamed renames name ∈ avoid) → ∀ name,
      (name ∈ (ts.map (·.freshenBindersAux avoid renames)).flatMap Ty.freeVars ↔
        ∃ original ∈ ts.flatMap Ty.freeVars, renamed renames original = name))
    generalizing avoid renames name with
  | var | int | bool => simp [Ty.freshenBindersAux, Ty.freeVars]
  | data n args ih =>
    simp only [Ty.freeVars] at covered
    simpa only [Ty.freshenBindersAux, Ty.freeVars] using ih avoid renames witness targets covered name
  | all body ih =>
    simp only [Ty.freeVars] at covered
    simpa only [Ty.freshenBindersAux, Ty.freeVars] using ih avoid renames witness targets covered name
  | arrow x a b ia ib =>
    let next := if avoid.contains x then freshTermName x (avoid ++ a.allTermNames ++ b.allTermNames) else x
    have fresh : next ∉ avoid := next_fresh avoid x a b
    have nextWitness : next ≠ valueName := fun h => fresh (h ▸ witness)
    have dom := ia avoid renames witness targets
      (fun n hn => covered n (by simp [Ty.freeVars, hn])) name
    have cod := ib (next :: avoid) ((x,next) :: renames) (by simp [witness])
      (by intro entry he; simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact nextWitness
          · exact targets entry he)
      (by
        intro n hn
        by_cases h : n = x
        · simp [renamed_cons, h]
        · simp only [renamed_cons, if_neg h, List.mem_cons]
          exact Or.inr (covered n (by simp [Ty.freeVars, hn, h]))) name
    simp only [Ty.freshenBindersAux, Ty.freeVars, List.mem_append, List.mem_filter, bne_iff_ne]
    change (_ ∨ _ ∧ name ≠ next) ↔ _
    rw [dom, cod]
    constructor
    · intro h
      rcases h with ⟨original, member, eq⟩ | ⟨⟨original, member, eq⟩, different⟩
      · exact ⟨original, Or.inl member, eq⟩
      · have ne : original ≠ x := by intro same; subst original; simp at eq; exact different eq.symm
        exact ⟨original, Or.inr ⟨member, ne⟩, by simpa [renamed_cons, ne] using eq⟩
    · rintro ⟨original, member, eq⟩
      rcases member with member | ⟨member, ne⟩
      · exact Or.inl ⟨original, member, eq⟩
      · refine Or.inr ⟨⟨original, member, by simpa [renamed_cons, ne] using eq⟩, ?_⟩
        intro same
        exact fresh ((eq.trans same) ▸ covered original (by simp [Ty.freeVars, member, ne]))
  | refine base atom ih =>
    have hb := ih avoid renames witness targets
      (fun n hn => covered n (by simp [Ty.freeVars, hn])) name
    simp only [Ty.freshenBindersAux, Ty.freeVars, Atom.renameNames_freeVars,
      List.mem_append, List.mem_filter, List.mem_map, bne_iff_ne]
    rw [hb]
    constructor
    · intro h
      rcases h with ⟨original, member, eq⟩ | ⟨⟨original, member, eq⟩, different⟩
      · exact ⟨original, Or.inl member, eq⟩
      · have ne : original ≠ valueName := by
          intro same; subst original
          rw [renamed_without_witness] at eq
          simp only [ite_true] at eq
          exact different eq.symm
        exact ⟨original, Or.inr ⟨member, ne⟩, by simpa [renamed_without_witness, ne] using eq⟩
    · rintro ⟨original, member, eq⟩
      rcases member with member | ⟨member, ne⟩
      · exact Or.inl ⟨original, member, eq⟩
      · refine Or.inr ⟨⟨original, member, by simpa [renamed_without_witness, ne] using eq⟩, ?_⟩
        exact fun h => renamed_ne_witness renames original targets ne (eq.trans h)
  | nil => simp
  | cons a as ia ib =>
    rename_i avoid renames witness targets covered name
    have ha := ia avoid renames witness targets (fun n hn => covered n (by simp [hn])) name
    have hb := ib avoid renames witness targets (fun n hn => covered n (by simp [hn])) name
    simp only [List.map_cons, List.flatMap_cons, List.mem_append, ha, hb]
    constructor
    · intro h
      rcases h with ⟨n, hn, eq⟩ | ⟨n, hn, eq⟩
      · exact ⟨n, Or.inl hn, eq⟩
      · exact ⟨n, Or.inr hn, eq⟩
    · rintro ⟨n, hn, eq⟩
      exact hn.elim (fun h => Or.inl ⟨n, h, eq⟩) (fun h => Or.inr ⟨n, h, eq⟩)

theorem Ty.freshenBinders_freeVars (type : Ty) (avoid : List String) (name : String) :
    name ∈ (type.freshenBinders avoid).freeVars ↔ name ∈ type.freeVars := by
  have h := type.freshenBindersAux_freeVars (valueName :: avoid ++ type.freeVars) []
    (by simp) (by simp) (by intro n hn; simp [hn]) name
  simpa [Ty.freshenBinders] using h

end LambdaRK

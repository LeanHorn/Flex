import Flex.VCG.LambdaRK.DatatypeSyntax
import Flex.VCG.LambdaRK.EnvironmentLemmas

/-! Interpretation lemmas for positive raw datatype declarations. -/
namespace LambdaRK

theorem Ty.freeVars_nil_of_raw (type : Ty) (raw : type.isRaw = true) : type.freeVars = [] := by
  induction type using Ty.rec
    (motive_2 := fun ts => (ts.map Ty.isRaw).all id = true → ts.flatMap Ty.freeVars = []) with
  | _ => simp_all [Ty.isRaw, Ty.freeVars]

theorem Ty.model_congr (signature : Signature) (assignment : KAssignment)
    (type : Ty) (left right : DataModel) (types : TypeEnvironment) (env : Environment)
    (agree : ∀ name ∈ type.dataNames, left.datatype name = right.datatype name) :
    type.denote signature left assignment types env =
      type.denote signature right assignment types env := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ types env,
      (∀ name ∈ ts.flatMap Ty.dataNames, left.datatype name = right.datatype name) →
      ts.map (Ty.denote signature left assignment types env) =
        ts.map (Ty.denote signature right assignment types env)) generalizing types env with
  | var => simp only [Ty.denote]
  | int => simp only [Ty.denote]
  | bool => simp only [Ty.denote]
  | data name args ih =>
    simp only [Ty.denote]
    rw [agree name (by simp [Ty.dataNames]), ih types env (fun n hn => agree n (by simp [Ty.dataNames, hn]))]
  | arrow name a b ia ib =>
    have ha := ia types env (fun n hn => agree n (by simp [Ty.dataNames, hn]))
    have hb (v : Value) := ib types (env.bind name v) (fun n hn => agree n (by simp [Ty.dataNames, hn]))
    simp only [Ty.denote, ha, hb]
  | all body ih => simp only [Ty.denote, ih _ env (by simpa [Ty.dataNames] using agree)]
  | refine base pred ih => simp only [Ty.denote, ih types env (by simpa [Ty.dataNames] using agree)]
  | nil => rfl
  | cons t ts ih it =>
    rename_i types env agree
    simp only [List.map_cons]
    rw [ih types env (fun n hn => agree n (by simp [hn])),
      it types env (fun n hn => agree n (by simp [hn]))]

/-- Inclusion for a single varying datatype, with all other interpretations fixed. -/
theorem Ty.denote_mono (signature : Signature) (assignment : KAssignment)
    (name : String) (left right : DataModel)
    (agree : ∀ other, other ≠ name → left.datatype other = right.datatype other)
    (included : ∀ args value, left.datatype name args value → right.datatype name args value)
    (type : Ty) (types : TypeEnvironment) (env : Environment)
    (positive : type.positiveIn name = true) (value : Value) :
    type.denote signature left assignment types env value →
      type.denote signature right assignment types env value := by
  induction type using Ty.rec
    (motive_2 := fun _ => True) generalizing types env value with
  | var => simp only [Ty.denote]; exact id
  | int => simp only [Ty.denote]; exact id
  | bool => simp only [Ty.denote]; exact id
  | data other args _ =>
    have arguments : args.map (Ty.denote signature left assignment types env) =
        args.map (Ty.denote signature right assignment types env) := by
      apply List.map_congr_left
      intro arg member
      apply arg.model_congr signature assignment left right types env
      intro n hn
      apply agree n
      intro equal
      subst n
      have fresh : name ∉ arg.dataNames := by
        simpa [Ty.positiveIn] using (List.all_eq_true.mp positive) arg member
      exact fresh hn
    simp only [Ty.denote, arguments]
    by_cases same : other = name
    · subst other; exact included _ value
    · rw [agree other same]; exact id
  | arrow binder a b _ ib =>
    simp only [Ty.positiveIn, Bool.and_eq_true] at positive
    have domain : a.denote signature left assignment types env =
        a.denote signature right assignment types env := by
      apply a.model_congr signature assignment left right types env
      intro n hn
      apply agree n
      intro equal
      subst n
      have fresh : name ∉ a.dataNames := by
        have := positive.1
        simpa [Ty.positiveIn] using this
      exact fresh hn
    have pos : b.positiveIn name = true := positive.2
    simp only [Ty.denote]
    intro h arg ha
    rw [← domain] at ha
    obtain ⟨result, app, ht⟩ := h arg ha
    exact ⟨result, app, ib types (env.bind binder arg) pos result ht⟩
  | all body ih =>
    simp only [Ty.denote]
    intro h candidate
    obtain ⟨result, app, ht⟩ := h candidate
    exact ⟨result, app, ih (candidate :: types) env positive result ht⟩
  | refine => simp [Ty.positiveIn] at positive
  | nil => trivial
  | cons => trivial

end LambdaRK

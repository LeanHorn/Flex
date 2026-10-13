import Flex.VCG.SystemFRK.Semantics

/-! Well-founded descent through constructor fields. -/
namespace SystemFRK

theorem Smaller.size_lt {small large : Value} (decrease : Smaller small large) :
    sizeOf small < sizeOf large := by
  induction decrease with
  | field member =>
    have := List.sizeOf_lt_of_mem member
    simp only [Value.ctor.sizeOf_spec]
    omega
  | trans _ _ left right => exact Nat.lt_trans left right

theorem Smaller.wellFounded : WellFounded Smaller :=
  Subrelation.wf (fun decrease => decrease.size_lt) (measure sizeOf).wf

theorem Smaller.irrefl (value : Value) : ¬ Smaller value value := by
  intro decrease
  have := decrease.size_lt
  omega

/-- The induction principle needed for recursive-call correctness. Its premise
contains only strict subvalues, never the current argument. -/
theorem Smaller.induction {motive : Value → Prop}
    (step : ∀ value, (∀ smaller, Smaller smaller value → motive smaller) → motive value)
    (value : Value) : motive value :=
  Smaller.wellFounded.induction value step

/-- Recursive calls may use correctness of strict subvalues only. -/
theorem Apply.recursiveClosure_total
    (signature : Signature) (environment : Environment) (binder : String) (body : Expr)
    (domain : Value → Prop) (post : Value → Value → Prop)
    (bodyCorrect : ∀ argument, domain argument →
      (∀ smaller, Smaller smaller argument → domain smaller →
        ∃ result, Apply signature (.recursiveClosure binder body environment) smaller result ∧
          post smaller result) →
      ∃ result, Eval signature (environment.bind binder argument)
          (some (.recursiveClosure binder body environment)) body result ∧
        post argument result) :
    ∀ argument, domain argument →
      ∃ result, Apply signature (.recursiveClosure binder body environment) argument result ∧
        post argument result := by
  intro argument
  induction argument using Smaller.induction with
  | step argument ih =>
    intro typed
    obtain ⟨result, evaluates, correct⟩ := bodyCorrect argument typed ih
    exact ⟨result, Apply.recursiveClosure evaluates, correct⟩

end SystemFRK

import Flex.VCG.SystemFRK.Binding.Substitution
import Flex.VCG.SystemFRK.Binding.Equality

/-! A separate comparison modulo named type binders. Ordinary `BEq Ty` remains
literal syntax equality. Fuel exhaustion only rejects a comparison. -/
namespace SystemFRK

def Ty.alphaEq : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
    match left, right with
    | .int, .int | .bool, .bool => true
    | .var i, .var j => i == j
    | .data a args, .data b others =>
      a == b && args.length == others.length &&
        (args.zip others).all (fun (x, y) => x.alphaEq fuel y)
    | .arrow x a b, .arrow y c d =>
      let name := freshTermName "$alpha" (valueName :: b.freeVars ++ d.freeVars)
      a.alphaEq fuel c && (b.substTerm x (.var name)).alphaEq fuel (d.substTerm y (.var name))
    | .all a, .all b => a.alphaEq fuel b
    | .refine a p, .refine b q => a.alphaEq fuel b && p == q
    | _, _ => false

private theorem renamed_codomain (body : Ty)
    {environment : Environment} {value : Value}
    (fresh : name ∉ body.freeVars) (reserved : name ≠ valueName) :
    (body.substTerm binder (.var name)).denote signature model assignment types
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
    simp [Environment.bind, List.lookup_cons, beq_eq_false_iff_ne.mpr same,
      beq_eq_false_iff_ne.mpr different]

private theorem map_eq_of_zip (xs ys : List Ty) (f : Ty → Candidate)
    (lengths : xs.length = ys.length)
    (same : ∀ pair ∈ xs.zip ys, f pair.1 = f pair.2) : xs.map f = ys.map f := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at lengths
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
      simp only [List.map_cons]
      rw [same (x,y) (by simp), ih ys lengths (fun pair h => same pair (by simp [h]))]

/-- Successful comparison preserves interpretation in every model and environment. -/
theorem Ty.alphaEq_denote (fuel : Nat) (left right : Ty)
    (equal : left.alphaEq fuel right = true)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) :
    left.denote signature model assignment types environment =
      right.denote signature model assignment types environment := by
  induction fuel generalizing left right types environment with
  | zero => simp [alphaEq] at equal
  | succ fuel ih =>
    cases left <;> cases right <;> simp only [alphaEq, Bool.and_eq_true, beq_iff_eq] at equal
    all_goals try contradiction
    case var.var i j => obtain rfl := equal; rfl
    case int.int => rfl
    case bool.bool => rfl
    case data.data a args b others =>
      obtain ⟨⟨rfl, lengths⟩, comparisons⟩ := equal
      simp only [Ty.denote]
      apply congrArg (model.datatype a)
      apply map_eq_of_zip _ _ _ lengths
      intro pair member
      exact ih pair.1 pair.2 (List.all_eq_true.mp comparisons pair member) types environment
    case arrow.arrow x a b y c d =>
      let name := freshTermName "$alpha" (valueName :: b.freeVars ++ d.freeVars)
      have fresh := freshTermName_not_mem "$alpha" (valueName :: b.freeVars ++ d.freeVars)
      have reserved : name ≠ valueName := fun eq => fresh (List.mem_cons.mpr (Or.inl eq))
      have fb : name ∉ b.freeVars := fun h => fresh (List.mem_cons_of_mem _ (List.mem_append_left _ h))
      have fd : name ∉ d.freeVars := fun h => fresh (List.mem_cons_of_mem _ (List.mem_append_right _ h))
      have domain := ih a c equal.1 types environment
      have codomain (v : Value) :
          b.denote signature model assignment types (environment.bind x v) =
          d.denote signature model assignment types (environment.bind y v) := by
        have h := ih _ _ equal.2 types (environment.bind name v)
        exact (renamed_codomain b fb reserved).symm.trans
          (h.trans (renamed_codomain d fd reserved))
      simp only [Ty.denote, domain]
      funext fn
      apply propext
      apply and_congr Iff.rfl
      apply forall_congr'; intro arg
      apply imp_congr_right; intro _
      apply exists_congr; intro result
      exact and_congr Iff.rfl (iff_of_eq (congrFun (codomain arg) result))
    case all.all a b =>
      simp only [Ty.denote]
      funext fn
      apply propext
      apply forall_congr'; intro candidate
      apply exists_congr; intro result
      exact and_congr Iff.rfl (iff_of_eq (congrFun (ih a b equal (candidate :: types) environment) result))
    case refine.refine a p b q =>
      obtain ⟨bases, rfl⟩ := equal
      simp only [Ty.denote, ih a b bases types environment]

end SystemFRK

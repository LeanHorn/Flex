import Flex.VCG.STLC.Interp
import Flex.VCG.STLC.Examples.Data

open STLC

/-! # Typing tests

  * **The checker, rule by rule** (`topVC`): a program each rule accepts, and
    where it matters a near miss it rejects.
  * **Declarative derivations** (`Hastype`), built directly from the rules.
  * **Semantic refutations**: by type safety, a program that gets stuck, or
    returns a value outside a type, has no typing derivation at all — not by
    any rule, in any combination. The interpreter supplies the run. -/

namespace STLC.Tests.Typing

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT
  DEnv.payload? DEnv.decl? DEnv.nCtors DEnv.instOK Ty.instTysOK Ty.instTysFrom Ty.instTys
  Cstr.conjAll List.finRange DEnv.var

/-! ## The checker, rule by rule -/

/-! ### Constants and subsumption -/

example (κ : KEnv) : topVC κ [] <| true |> <ty| Bool{ν : ν = true} |> := by simp [topVC]

example (κ : KEnv) : ¬ topVC κ [] <| true |> <ty| Bool{ν : ν = false} |> := by simp [topVC]; exact ⟨REnv.empty, trivial⟩

/-- A literal's exact type `{ν = 5}` is a subtype of `{0 ≤ ν}`… -/
example (κ : KEnv) : topVC κ [] <| 5 |> <ty| Int{ν : 0 ≤ ν} |> := by simp [topVC]

/-- …but not of `{ν = 6}`. -/
example (κ : KEnv) : ¬ topVC κ [] <| 5 |> (IntN 6) := by simp [topVC]; exact ⟨REnv.empty, trivial⟩

/-! ### Annotations -/

/-- An annotation is checked, and then synthesized. -/
example (κ : KEnv) : topVC κ [] <| (5 : ⌜Pos⌝) |> NatT := by simp [topVC]; intros; omega

/-- The annotation hides the exact value: `(5 : Pos)` is not known to be `5`. -/
example (κ : KEnv) : ¬ topVC κ [] <| (5 : ⌜Pos⌝) |> (IntN 5) := by
  simp [topVC]; exact ⟨REnv.empty, 6, by omega⟩

/-! ### Primitive operations (on variables, in A-normal form) -/

example (κ : KEnv) : topVC κ [] <| λ x y, x + y |>
    <ty| (x : Int) -> (y : Int) -> Int{ν : ν = x + y} |> := by simp [topVC]

example (κ : KEnv) : topVC κ [] <| λ b, ¬b |>
    <ty| (b : Bool) -> Bool{ν : ν = ¬b} |> := by simp [topVC]

example (κ : KEnv) : topVC κ [] <| λ a b, a ∧ b |>
    <ty| (a : Bool) -> (b : Bool) -> Bool{ν : ν = (a ∧ b)} |> := by simp [topVC]

/-- Comparison at `Bool`. -/
example (κ : KEnv) : topVC κ [] <| λ a b, a ≤ b |>
    <ty| (a : Bool) -> (b : Bool) -> Bool{ν : ν = true ↔ a ≤ b} |> := by simp [topVC]

/-- Comparison at a `B`-kinded type variable. -/
example (κ : KEnv) : topVC κ [] <| Λ α : B, λ x y, x ≤ y |>
    <ty| ∀ α : B, (x : α) -> (y : α) -> Bool{ν : ν = true ↔ x ≤ y} |> := by simp [topVC]

/-- …but not at a `⋆`-kinded one, which may hold functions. -/
example (κ : KEnv) : ¬ topVC κ [] <| Λ α : ⋆, λ x y, x ≤ y |>
    <ty| ∀ α : ⋆, α -> α -> Bool |> := by simp [topVC]

/-- The primitives take variables: `1 + 2` must be let-bound first. -/
example (κ : KEnv) : ¬ topVC κ [] <| 1 + 2 |> TT := by simp [topVC]

/-! ### Functions and application -/

/-- The result type of an application mentions the argument. -/
example (κ : KEnv) : topVC κ []
    <| let inc : ⌜incTy⌝ = ⌜incE⌝ in let three = 3 in inc three |> (IntN 4) := by simp [topVC]

example (κ : KEnv) : ¬ topVC κ []
    <| let inc : ⌜incTy⌝ = ⌜incE⌝ in let three = 3 in inc three |> (IntN 3) := by simp [topVC]; exact ⟨REnv.empty, trivial⟩

/-- The argument must be a variable. -/
example (κ : KEnv) : ¬ topVC κ [] <| let inc : ⌜incTy⌝ = ⌜incE⌝ in inc 3 |> TT := by simp [topVC]

/-- Function subtyping: contravariant in the argument, covariant in the result. -/
example (κ : KEnv) : topVC κ [] <| λ f, f |>
    <ty| (Int -> ⌜Pos⌝) -> (⌜Pos⌝ -> Int) |> := by simp [topVC]

example (κ : KEnv) : ¬ topVC κ [] <| λ f, f |>
    <ty| (⌜Pos⌝ -> Int) -> (Int -> Int) |> := by
  simp [topVC]; exact ⟨REnv.empty, 0, by omega⟩

/-! ### Conditionals are path-sensitive -/

/-- `max(0, x)` is a natural number: each branch knows the test's outcome. -/
example (κ : KEnv) : topVC κ [] <| λ x, let z = 0 in let c = x ≤ z in if c then z else x |>
    <ty| Int -> ⌜NatT⌝ |> := by
  simp [topVC]; intros; omega

/-- Swapping the branches breaks it. -/
example (κ : KEnv) : ¬ topVC κ [] <| λ x, let z = 0 in let c = x ≤ z in if c then x else z |>
    <ty| Int -> ⌜NatT⌝ |> := by
  simp [topVC]; exact ⟨REnv.empty, -1, by omega⟩

/-- `unreachable` checks only where the context is contradictory. -/
example (κ : KEnv) : ¬ topVC κ [] <| unreachable |> TT := by
  simp [topVC]; exact ⟨REnv.empty, trivial⟩

/-! ### Recursion -/

/-- `count n` counts down to `0`, so it returns `0`. -/
abbrev countE : Exp :=
  <| fix count n, let z = 0 in let c = n ≤ z in
       if c then z else let m = -1 in let n1 = n + m in count n1 |>

example (κ : KEnv) : topVC κ [] countE <ty| Int -> Int{ν : ν = 0} |> := by simp [topVC]

/-- The recursive call is checked against the same specification. -/
example (κ : KEnv) : ¬ topVC κ [] countE <ty| Int -> Int{ν : ν = 1} |> := by
  simp [topVC]; exact ⟨REnv.empty, 0, by omega⟩

/-! ### Polymorphism -/

abbrev constE : Exp := <| Λ α : ⋆, Λ β : ⋆, λ x y, x |>

example (κ : KEnv) : topVC κ [] constE <ty| ∀ α : ⋆, ∀ β : ⋆, α -> β -> α |> := by
  simp [topVC]

/-- Parametricity at work: `const` cannot return its second argument. -/
example (κ : KEnv) : ¬ topVC κ [] <| Λ α : ⋆, Λ β : ⋆, λ x y, y |>
    <ty| ∀ α : ⋆, ∀ β : ⋆, α -> β -> α |> := by simp [topVC]

/-- Instantiating a `B` variable with a refined base… -/
example (κ : KEnv) : topVC κ []
    <| let id : ⌜idTy⌝ = ⌜idPoly⌝ in let t = true in id[Bool] t |>
    <ty| Bool{ν : ν = true} |> := by simp [topVC]

/-- …but not with a function type: its kind is `⋆`. -/
example (κ : KEnv) : ¬ topVC κ []
    <| let id : ⌜idTy⌝ = ⌜idPoly⌝ in let f = λ x, x in id[Int -> Int] f |>
    <ty| Int -> Int |> := by simp [topVC]

/-! ### Dependent pairs -/

abbrev OrdPair : Ty := <ty| (x : Int) × Int{ν : x ≤ ν} |>

example (κ : KEnv) : topVC κ [] <| let a = 1 in let b = 2 in (a, b) |> OrdPair := by
  simp [topVC]

example (κ : KEnv) : ¬ topVC κ [] <| let a = 2 in let b = 1 in (a, b) |> OrdPair := by
  simp [topVC]; exact ⟨REnv.empty, trivial⟩

/-- Splitting a pair recovers the dependency between its components. -/
example (κ : KEnv) : topVC κ [] <| λ p, let (x, y) = p in x ≤ y |>
    <ty| ⌜OrdPair⌝ -> Bool{ν : ν = true} |> := by simp [topVC]

/-- Without it, the comparison could go either way. -/
example (κ : KEnv) : ¬ topVC κ [] <| λ p, let (x, y) = p in x ≤ y |>
    <ty| (Int × Int) -> Bool{ν : ν = true} |> := by
  simp [topVC]; exact ⟨REnv.empty, 1, 0, by omega⟩

/-! ### Datatypes -/

/-- A constructor's payload is checked against the field types. -/
example (κ : KEnv) : topVC κ [] <| let one = 1 in Some[⌜Pos⌝] one |> <ty| option[⌜Pos⌝] |>
    optionEnv := by simp [topVC, optionEnv, optionDecl]

example (κ : KEnv) : ¬ topVC κ [] <| let zero = 0 in Some[⌜Pos⌝] zero |> <ty| option[⌜Pos⌝] |>
    optionEnv := by simp [topVC, optionEnv, optionDecl]; exact ⟨REnv.empty, trivial⟩

/-- Each alternative is checked with its constructor's fields in scope. -/
example (κ : KEnv) : topVC κ [] <| λ o, match o with | None => 1 | Some x => x |>
    <ty| option[⌜Pos⌝] -> ⌜Pos⌝ |> optionEnv := by simp [topVC, optionEnv, optionDecl]

example (κ : KEnv) : ¬ topVC κ [] <| λ o, match o with | None => 0 | Some x => x |>
    <ty| option[⌜Pos⌝] -> ⌜Pos⌝ |> optionEnv := by simp [topVC, optionEnv, optionDecl]; exact ⟨REnv.empty, trivial⟩

/-- A constructor of an undeclared datatype is rejected. -/
example (κ : KEnv) : ¬ topVC κ [] <| let one = 1 in Some[Int] one |> <ty| option[Int] |> := by
  simp [topVC]

/-! ## Declarative derivations -/

example (κ : KEnv) : Hastype [] κ [("x", TT)] (.fvar "x") (self [] "x" TT) :=
  .var rfl (by decide)

example (κ : KEnv) :
    Hastype [] κ [("x", TT), ("y", TT)] (.add (.fvar "x") (.fvar "y"))
      (.refine .int (.fmla (.eq .int (.bvar .int 0) (.add (.fvar .int "x") (.fvar .int "y"))))) :=
  .add_var rfl rfl

example (κ : KEnv) :
    Hastype [] κ [("a", <ty| Bool |>), ("b", <ty| Bool |>)] (.leq (.fvar "a") (.fvar "b"))
      (leqTy .bool "a" "b") :=
  .leq_var rfl rfl rfl

example (κ : KEnv) :
    Hastype [] κ [("b", <ty| Bool |>)] (.not (.fvar "b"))
      (.refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.not (.fvar .bool "b"))))) :=
  .not_var rfl

/-- Subsumption: `5 : {ν = 5} <: Pos`. -/
example (κ : KEnv) : Hastype [] κ [] (.iconst 5) Pos :=
  .sub .int_const
    (.refine (x := "x") (by decide) fun γ hγ => by
      simp [ModelsEnv, Ty.hyp?] at hγ ⊢; omega)
    (by decide)

/-- `unreachable` is typeable in a contradictory context — here one that
    assumes `x : {ν : Int | false}`. -/
example (κ : KEnv) : Hastype [] κ [("x", <ty| Int{ν : ⊥} |>)] .unreach (IntN 42) :=
  .unreach (fun γ hγ => by simp [ModelsEnv, Ty.hyp?] at hγ) (by decide)

/-- Type abstraction, with an explicit fresh type variable. -/
example (κ : KEnv) : Hastype [] κ [] <| Λ α : ⋆, 3 |> <ty| ∀ α : ⋆, Int{ν : ν = 3} |> :=
  .tabs (a := ("a", .star)) (by decide) rfl (by simp) .int_const

/-! ## Semantic refutations

  Type safety turns a run into a refutation of *every* typing derivation. -/

/-- A program that gets stuck has no type. -/
theorem not_hastype_of_stuck {de : DEnv} {κ : KEnv} {e : Exp} {t : Ty} (hde : de.wfB = true)
    {g n : Nat} (h : runI g n e = .stuck) : ¬ Hastype de κ [] e t := fun ht =>
  runI_stuck h (let ⟨o, ho, _⟩ := type_safety hde ht n; ⟨o, ho⟩)

/-- A value a program of refined base type returns satisfies the refinement. -/
theorem hastype_refine_run {de : DEnv} {κ : KEnv} {e : Exp} {b : Base} {r : Refinement}
    (hde : de.wfB = true) (ht : Hastype de κ [] e (.refine b r))
    {n m : Nat} {v : Val} (hev : Run n e (.val v m)) :
    Refinement.interp κ r ({ REnv.empty with sorts := { meas := de.measEval } }.push v) := by
  obtain ⟨o, hev', hres⟩ := type_safety hde ht n
  cases Eval.det hev hev'
  have e : REnv.empty.withSorts (TyEnvSem.empty de).sorts =
      { REnv.empty with sorts := { meas := de.measEval } } := by
    apply REnv.ext <;> try rfl
    simp only [TyEnvSem.sorts, TyEnvSem.empty]
    congr 1
    funext a
    rcases a with ⟨_, _ | _⟩ <;> rfl
  have := hres v m rfl
  simp only [TyDenote, e] at this
  exact this.2

example (κ : KEnv) (t : Ty) : ¬ Hastype [] κ [] <| unreachable |> t :=
  not_hastype_of_stuck rfl (g := 10) (n := 0) rfl

example (κ : KEnv) (t : Ty) : ¬ Hastype [] κ [] <| let x = 1 in let b = true in x + b |> t :=
  not_hastype_of_stuck rfl (g := 10) (n := 0) rfl

/-- Applying an integer. -/
example (κ : KEnv) (t : Ty) : ¬ Hastype [] κ [] <| let f = 3 in let x = 4 in f x |> t :=
  not_hastype_of_stuck rfl (g := 10) (n := 0) rfl

/-- Stuck only after a call: the refutation sees through the function. -/
example (κ : KEnv) (t : Ty) :
    ¬ Hastype [] κ [] <| let f = λ x, if x then 1 else 2 in let y = 0 in f y |> t :=
  not_hastype_of_stuck rfl (g := 10) (n := 1) rfl

/-- Matching on a pair, and splitting a constructor. -/
example (κ : KEnv) (t : Ty) :
    ¬ Hastype optionEnv κ [] <| let p = (1, 2) in match p with | None => 0 | Some x => x |> t :=
  not_hastype_of_stuck rfl (g := 10) (n := 1) rfl

example (κ : KEnv) (t : Ty) :
    ¬ Hastype optionEnv κ [] <| let o = None[Int] in let (x, y) = o in x |> t :=
  not_hastype_of_stuck rfl (g := 10) (n := 1) rfl

/-- `2 + 3` is not `6`, whatever rules are used. -/
example (κ : KEnv) : ¬ Hastype [] κ [] <| let x = 2 in let y = 3 in x + y |> (IntN 6) := fun ht => by
  have := hastype_refine_run rfl ht (n := 0) (by by_interp : Run 0 _ (.val (.iconst 5) 0))
  simp [Refinement.interp, Formula.interp, Term.interp] at this

/-- `sum 3 = 6`, so no derivation gives `sum 3` the type `{ν ≤ 5}`. -/
example (κ : KEnv) :
    ¬ Hastype [] κ [] <| let sum : ⌜sumTy⌝ = ⌜sumE⌝ in let three = 3 in sum three |>
      <ty| Int{ν : ν ≤ 5} |> := fun ht => by
  have := hastype_refine_run rfl ht (n := 10) (by by_interp : Run 10 _ (.val (.iconst 6) 6))
  simp [Refinement.interp, Formula.interp, Term.interp] at this

end STLC.Tests.Typing

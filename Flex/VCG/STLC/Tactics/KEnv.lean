import Flex.VCG.STLC.Spec.Syntax

open STLC

namespace STLC

/-! ## KEnv construction helpers

  `KPred n` is the type of n-ary curried Int predicates.
  `liftKPred n` lifts a `KPred n` into the heterogeneous-list form expected
  by `KEnv`: it peels Int values off the front of the arg list one at a time.
  `mkKEnv` builds a `KEnv` from a finite name→predicate list, defaulting to
  `True` for unmentioned keys. `exists_kenv_curried` is the sufficiency lemma
  used by `intro_kenv` to replace `∃ κ : KEnv, P κ` with individual curried
  existentials. -/

/-- `KPred n` = `Int → Int → … → Int → Prop` (n arguments, curried). -/
@[reducible]
def KPred : Nat → Type
  | 0     => Prop
  | n + 1 => Int → KPred n

/-- Lift a curried `KPred n` to operate on a heterogeneous arg list.
    Returns `True` on arity or type mismatch. -/
def liftKPred : (n : Nat) → KPred n → List (Σ b : Base, b.interp) → Prop
  | 0,     p, []                    => p
  | 0,     _, _                     => True
  | _ + 1, _, []                    => True
  | n + 1, f, (⟨.int,  v⟩ :: rest) => liftKPred n (f v) rest
  | _ + 1, _, _                     => True

@[simp] theorem liftKPred_zero (p : Prop) :
    liftKPred 0 p [] = p := rfl

@[simp] theorem liftKPred_succ_int (n : Nat) (f : Int → KPred n) (v : Int)
    (rest : List (Σ b : Base, b.interp)) :
    liftKPred (n + 1) f (⟨.int, v⟩ :: rest) = liftKPred n (f v) rest := rfl


def mkKEnv (ks : List (KVar × (List (Σ b : Base, b.interp) → Prop))) : KEnv :=
  fun name => (ks.lookup name).getD (fun _ => True)

theorem exists_kenv_curried {P : KEnv → Prop}
    (ks : List (KVar × (List (Σ b : Base, b.interp) → Prop)))
    (h : P (mkKEnv ks)) : ∃ κ : KEnv, P κ :=
  ⟨mkKEnv ks, h⟩

end STLC

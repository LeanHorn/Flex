import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiFdRenumber
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiFdRenumberQualifs

@[qualif]
def EqTrue (v_from₀ : Prop) : Prop :=
  v_from₀

@[qualif]
def EqFalse (v_from₀ : Prop) : Prop :=
  (¬v_from₀)

@[qualif]
def EqZero (v_from₀ : Int) : Prop :=
  (v_from₀ = 0)

@[qualif]
def GtZero (v_from₀ : Int) : Prop :=
  (v_from₀ > 0)

@[qualif]
def GeZero (v_from₀ : Int) : Prop :=
  (v_from₀ ≥ 0)

@[qualif]
def LtZero (v_from₀ : Int) : Prop :=
  (v_from₀ < 0)

@[qualif]
def LeZero (v_from₀ : Int) : Prop :=
  (v_from₀ ≤ 0)

@[qualif]
def Eq (v_from₀ : Int) (v_to₀ : Int) : Prop :=
  (v_from₀ = v_to₀)

@[qualif]
def Gt (v_from₀ : Int) (v_to₀ : Int) : Prop :=
  (v_from₀ > v_to₀)

@[qualif]
def Ge (v_from₀ : Int) (v_to₀ : Int) : Prop :=
  (v_from₀ ≥ v_to₀)

@[qualif]
def Lt (v_from₀ : Int) (v_to₀ : Int) : Prop :=
  (v_from₀ < v_to₀)

@[qualif]
def Le (v_from₀ : Int) (v_to₀ : Int) : Prop :=
  (v_from₀ ≤ v_to₀)

@[qualif]
def Le1 (v_from₀ : Int) (v_to₀ : Int) : Prop :=
  (v_from₀ ≤ (v_to₀ - 1))

end WrappersWasiFdRenumberQualifs

open WrappersWasiFdRenumberQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiFdRenumber_proof : WrappersWasiFdRenumber := by
  unfold WrappersWasiFdRenumber
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

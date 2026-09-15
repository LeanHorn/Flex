import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecDequeImpl__1__HandleCapacityIncrease
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecDequeImpl1HandleCapacityIncreaseQualifs

@[qualif]
def EqTrue (new_capacity₀ : Prop) : Prop :=
  new_capacity₀

@[qualif]
def EqFalse (new_capacity₀ : Prop) : Prop :=
  (¬new_capacity₀)

@[qualif]
def EqZero (new_capacity₀ : Int) : Prop :=
  (new_capacity₀ = 0)

@[qualif]
def GtZero (new_capacity₀ : Int) : Prop :=
  (new_capacity₀ > 0)

@[qualif]
def GeZero (new_capacity₀ : Int) : Prop :=
  (new_capacity₀ ≥ 0)

@[qualif]
def LtZero (new_capacity₀ : Int) : Prop :=
  (new_capacity₀ < 0)

@[qualif]
def LeZero (new_capacity₀ : Int) : Prop :=
  (new_capacity₀ ≤ 0)

@[qualif]
def Eq (new_capacity₀ : Int) (a'₁ : Int) : Prop :=
  (new_capacity₀ = a'₁)

@[qualif]
def Gt (new_capacity₀ : Int) (a'₁ : Int) : Prop :=
  (new_capacity₀ > a'₁)

@[qualif]
def Ge (new_capacity₀ : Int) (a'₁ : Int) : Prop :=
  (new_capacity₀ ≥ a'₁)

@[qualif]
def Lt (new_capacity₀ : Int) (a'₁ : Int) : Prop :=
  (new_capacity₀ < a'₁)

@[qualif]
def Le (new_capacity₀ : Int) (a'₁ : Int) : Prop :=
  (new_capacity₀ ≤ a'₁)

@[qualif]
def Le1 (new_capacity₀ : Int) (a'₁ : Int) : Prop :=
  (new_capacity₀ ≤ (a'₁ - 1))

end VecDequeImpl1HandleCapacityIncreaseQualifs

open VecDequeImpl1HandleCapacityIncreaseQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecDequeImpl__1__HandleCapacityIncrease_proof : VecDequeImpl__1__HandleCapacityIncrease := by
  unfold VecDequeImpl__1__HandleCapacityIncrease
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecDequeImpl__1__WrapSub
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecDequeImpl1WrapSubQualifs

@[qualif]
def EqTrue (idx₀ : Prop) : Prop :=
  idx₀

@[qualif]
def EqFalse (idx₀ : Prop) : Prop :=
  (¬idx₀)

@[qualif]
def EqZero (idx₀ : Int) : Prop :=
  (idx₀ = 0)

@[qualif]
def GtZero (idx₀ : Int) : Prop :=
  (idx₀ > 0)

@[qualif]
def GeZero (idx₀ : Int) : Prop :=
  (idx₀ ≥ 0)

@[qualif]
def LtZero (idx₀ : Int) : Prop :=
  (idx₀ < 0)

@[qualif]
def LeZero (idx₀ : Int) : Prop :=
  (idx₀ ≤ 0)

@[qualif]
def Eq (idx₀ : Int) (subtrahend₀ : Int) : Prop :=
  (idx₀ = subtrahend₀)

@[qualif]
def Gt (idx₀ : Int) (subtrahend₀ : Int) : Prop :=
  (idx₀ > subtrahend₀)

@[qualif]
def Ge (idx₀ : Int) (subtrahend₀ : Int) : Prop :=
  (idx₀ ≥ subtrahend₀)

@[qualif]
def Lt (idx₀ : Int) (subtrahend₀ : Int) : Prop :=
  (idx₀ < subtrahend₀)

@[qualif]
def Le (idx₀ : Int) (subtrahend₀ : Int) : Prop :=
  (idx₀ ≤ subtrahend₀)

@[qualif]
def Le1 (idx₀ : Int) (subtrahend₀ : Int) : Prop :=
  (idx₀ ≤ (subtrahend₀ - 1))

end VecDequeImpl1WrapSubQualifs

open VecDequeImpl1WrapSubQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecDequeImpl__1__WrapSub_proof : VecDequeImpl__1__WrapSub := by
  unfold VecDequeImpl__1__WrapSub
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecDequeImpl__3__WithCapacityIn
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecDequeImpl3WithCapacityInQualifs

@[qualif]
def EqTrue (alloc₀ : Prop) : Prop :=
  alloc₀

@[qualif]
def EqFalse (alloc₀ : Prop) : Prop :=
  (¬alloc₀)

@[qualif]
def EqZero (alloc₀ : Int) : Prop :=
  (alloc₀ = 0)

@[qualif]
def GtZero (alloc₀ : Int) : Prop :=
  (alloc₀ > 0)

@[qualif]
def GeZero (alloc₀ : Int) : Prop :=
  (alloc₀ ≥ 0)

@[qualif]
def LtZero (alloc₀ : Int) : Prop :=
  (alloc₀ < 0)

@[qualif]
def LeZero (alloc₀ : Int) : Prop :=
  (alloc₀ ≤ 0)

@[qualif]
def Eq (alloc₀ : Int) (cap₀ : Int) : Prop :=
  (alloc₀ = cap₀)

@[qualif]
def Gt (alloc₀ : Int) (cap₀ : Int) : Prop :=
  (alloc₀ > cap₀)

@[qualif]
def Ge (alloc₀ : Int) (cap₀ : Int) : Prop :=
  (alloc₀ ≥ cap₀)

@[qualif]
def Lt (alloc₀ : Int) (cap₀ : Int) : Prop :=
  (alloc₀ < cap₀)

@[qualif]
def Le (alloc₀ : Int) (cap₀ : Int) : Prop :=
  (alloc₀ ≤ cap₀)

@[qualif]
def Le1 (alloc₀ : Int) (cap₀ : Int) : Prop :=
  (alloc₀ ≤ (cap₀ - 1))

end VecDequeImpl3WithCapacityInQualifs

open VecDequeImpl3WithCapacityInQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecDequeImpl__3__WithCapacityIn_proof : VecDequeImpl__3__WithCapacityIn := by
  unfold VecDequeImpl__3__WithCapacityIn
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

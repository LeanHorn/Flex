import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecDequeImpl__3__NewIn
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecDequeImpl3NewInQualifs

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
def Eq (alloc₀ : Int) (a'₁ : Int) : Prop :=
  (alloc₀ = a'₁)

@[qualif]
def Gt (alloc₀ : Int) (a'₁ : Int) : Prop :=
  (alloc₀ > a'₁)

@[qualif]
def Ge (alloc₀ : Int) (a'₁ : Int) : Prop :=
  (alloc₀ ≥ a'₁)

@[qualif]
def Lt (alloc₀ : Int) (a'₁ : Int) : Prop :=
  (alloc₀ < a'₁)

@[qualif]
def Le (alloc₀ : Int) (a'₁ : Int) : Prop :=
  (alloc₀ ≤ a'₁)

@[qualif]
def Le1 (alloc₀ : Int) (a'₁ : Int) : Prop :=
  (alloc₀ ≤ (a'₁ - 1))

end VecDequeImpl3NewInQualifs

open VecDequeImpl3NewInQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecDequeImpl__3__NewIn_proof : VecDequeImpl__3__NewIn := by
  unfold VecDequeImpl__3__NewIn
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

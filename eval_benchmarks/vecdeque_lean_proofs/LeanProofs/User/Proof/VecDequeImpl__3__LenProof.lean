import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecDequeImpl__3__Len
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecDequeImpl3LenQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ = v₁)

@[qualif]
def Gt (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ > v₁)

@[qualif]
def Ge (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ ≥ v₁)

@[qualif]
def Lt (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ < v₁)

@[qualif]
def Le (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ ≤ v₁)

@[qualif]
def Le1 (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ ≤ (v₁ - 1))

end VecDequeImpl3LenQualifs

open VecDequeImpl3LenQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecDequeImpl__3__Len_proof : VecDequeImpl__3__Len := by
  unfold VecDequeImpl__3__Len
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

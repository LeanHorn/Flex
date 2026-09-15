import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.IovParseIovs
open Classical
set_option linter.unusedVariables false


namespace F

namespace IovParseIovsQualifs

@[qualif]
def EqTrue (ctx₀ : Prop) : Prop :=
  ctx₀

@[qualif]
def EqFalse (ctx₀ : Prop) : Prop :=
  (¬ctx₀)

@[qualif]
def EqZero (ctx₀ : Int) : Prop :=
  (ctx₀ = 0)

@[qualif]
def GtZero (ctx₀ : Int) : Prop :=
  (ctx₀ > 0)

@[qualif]
def GeZero (ctx₀ : Int) : Prop :=
  (ctx₀ ≥ 0)

@[qualif]
def LtZero (ctx₀ : Int) : Prop :=
  (ctx₀ < 0)

@[qualif]
def LeZero (ctx₀ : Int) : Prop :=
  (ctx₀ ≤ 0)

@[qualif]
def Eq (ctx₀ : Int) (iovs₀ : Int) : Prop :=
  (ctx₀ = iovs₀)

@[qualif]
def Gt (ctx₀ : Int) (iovs₀ : Int) : Prop :=
  (ctx₀ > iovs₀)

@[qualif]
def Ge (ctx₀ : Int) (iovs₀ : Int) : Prop :=
  (ctx₀ ≥ iovs₀)

@[qualif]
def Lt (ctx₀ : Int) (iovs₀ : Int) : Prop :=
  (ctx₀ < iovs₀)

@[qualif]
def Le (ctx₀ : Int) (iovs₀ : Int) : Prop :=
  (ctx₀ ≤ iovs₀)

@[qualif]
def Le1 (ctx₀ : Int) (iovs₀ : Int) : Prop :=
  (ctx₀ ≤ (iovs₀ - 1))

end IovParseIovsQualifs

open IovParseIovsQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def IovParseIovs_proof : IovParseIovs := by
  unfold IovParseIovs
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

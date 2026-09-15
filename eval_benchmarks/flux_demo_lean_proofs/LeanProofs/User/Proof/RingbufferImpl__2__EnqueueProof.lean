import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RingbufferImpl__2__Enqueue
open Classical
set_option linter.unusedVariables false


namespace F

namespace RingbufferImpl2EnqueueQualifs

@[qualif]
def EqTrue (val₀ : Prop) : Prop :=
  val₀

@[qualif]
def EqFalse (val₀ : Prop) : Prop :=
  (¬val₀)

@[qualif]
def EqZero (val₀ : Int) : Prop :=
  (val₀ = 0)

@[qualif]
def GtZero (val₀ : Int) : Prop :=
  (val₀ > 0)

@[qualif]
def GeZero (val₀ : Int) : Prop :=
  (val₀ ≥ 0)

@[qualif]
def LtZero (val₀ : Int) : Prop :=
  (val₀ < 0)

@[qualif]
def LeZero (val₀ : Int) : Prop :=
  (val₀ ≤ 0)

@[qualif]
def Eq (val₀ : Int) (j₀ : Int) : Prop :=
  (val₀ = j₀)

@[qualif]
def Gt (val₀ : Int) (j₀ : Int) : Prop :=
  (val₀ > j₀)

@[qualif]
def Ge (val₀ : Int) (j₀ : Int) : Prop :=
  (val₀ ≥ j₀)

@[qualif]
def Lt (val₀ : Int) (j₀ : Int) : Prop :=
  (val₀ < j₀)

@[qualif]
def Le (val₀ : Int) (j₀ : Int) : Prop :=
  (val₀ ≤ j₀)

@[qualif]
def Le1 (val₀ : Int) (j₀ : Int) : Prop :=
  (val₀ ≤ (j₀ - 1))

end RingbufferImpl2EnqueueQualifs

open RingbufferImpl2EnqueueQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RingbufferImpl__2__Enqueue_proof : RingbufferImpl__2__Enqueue := by
  unfold RingbufferImpl__2__Enqueue
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

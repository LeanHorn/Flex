import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.PollWritebackTimeouts
open Classical
set_option linter.unusedVariables false


namespace F

namespace PollWritebackTimeoutsQualifs

@[qualif]
def EqTrue (out_ptr₀ : Prop) : Prop :=
  out_ptr₀

@[qualif]
def EqFalse (out_ptr₀ : Prop) : Prop :=
  (¬out_ptr₀)

@[qualif]
def EqZero (out_ptr₀ : Int) : Prop :=
  (out_ptr₀ = 0)

@[qualif]
def GtZero (out_ptr₀ : Int) : Prop :=
  (out_ptr₀ > 0)

@[qualif]
def GeZero (out_ptr₀ : Int) : Prop :=
  (out_ptr₀ ≥ 0)

@[qualif]
def LtZero (out_ptr₀ : Int) : Prop :=
  (out_ptr₀ < 0)

@[qualif]
def LeZero (out_ptr₀ : Int) : Prop :=
  (out_ptr₀ ≤ 0)

@[qualif]
def Eq (out_ptr₀ : Int) (timeouts₀ : Int) : Prop :=
  (out_ptr₀ = timeouts₀)

@[qualif]
def Gt (out_ptr₀ : Int) (timeouts₀ : Int) : Prop :=
  (out_ptr₀ > timeouts₀)

@[qualif]
def Ge (out_ptr₀ : Int) (timeouts₀ : Int) : Prop :=
  (out_ptr₀ ≥ timeouts₀)

@[qualif]
def Lt (out_ptr₀ : Int) (timeouts₀ : Int) : Prop :=
  (out_ptr₀ < timeouts₀)

@[qualif]
def Le (out_ptr₀ : Int) (timeouts₀ : Int) : Prop :=
  (out_ptr₀ ≤ timeouts₀)

@[qualif]
def Le1 (out_ptr₀ : Int) (timeouts₀ : Int) : Prop :=
  (out_ptr₀ ≤ (timeouts₀ - 1))

end PollWritebackTimeoutsQualifs

open PollWritebackTimeoutsQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def PollWritebackTimeouts_proof : PollWritebackTimeouts := by
  unfold PollWritebackTimeouts
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

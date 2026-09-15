import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiPathReadlink
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiPathReadlinkQualifs

@[qualif]
def EqTrue (v_fd₀ : Prop) : Prop :=
  v_fd₀

@[qualif]
def EqFalse (v_fd₀ : Prop) : Prop :=
  (¬v_fd₀)

@[qualif]
def EqZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ = 0)

@[qualif]
def GtZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ > 0)

@[qualif]
def GeZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ ≥ 0)

@[qualif]
def LtZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ < 0)

@[qualif]
def LeZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ ≤ 0)

@[qualif]
def Eq (v_fd₀ : Int) (pathname₀ : Int) : Prop :=
  (v_fd₀ = pathname₀)

@[qualif]
def Gt (v_fd₀ : Int) (pathname₀ : Int) : Prop :=
  (v_fd₀ > pathname₀)

@[qualif]
def Ge (v_fd₀ : Int) (pathname₀ : Int) : Prop :=
  (v_fd₀ ≥ pathname₀)

@[qualif]
def Lt (v_fd₀ : Int) (pathname₀ : Int) : Prop :=
  (v_fd₀ < pathname₀)

@[qualif]
def Le (v_fd₀ : Int) (pathname₀ : Int) : Prop :=
  (v_fd₀ ≤ pathname₀)

@[qualif]
def Le1 (v_fd₀ : Int) (pathname₀ : Int) : Prop :=
  (v_fd₀ ≤ (pathname₀ - 1))

end WrappersWasiPathReadlinkQualifs

open WrappersWasiPathReadlinkQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiPathReadlink_proof : WrappersWasiPathReadlink := by
  unfold WrappersWasiPathReadlink
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

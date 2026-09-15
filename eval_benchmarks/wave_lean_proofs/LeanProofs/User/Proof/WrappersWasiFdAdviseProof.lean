import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiFdAdvise
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiFdAdviseQualifs

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
def Eq (ctx₀ : Int) (v_fd₀ : Int) : Prop :=
  (ctx₀ = v_fd₀)

@[qualif]
def Gt (ctx₀ : Int) (v_fd₀ : Int) : Prop :=
  (ctx₀ > v_fd₀)

@[qualif]
def Ge (ctx₀ : Int) (v_fd₀ : Int) : Prop :=
  (ctx₀ ≥ v_fd₀)

@[qualif]
def Lt (ctx₀ : Int) (v_fd₀ : Int) : Prop :=
  (ctx₀ < v_fd₀)

@[qualif]
def Le (ctx₀ : Int) (v_fd₀ : Int) : Prop :=
  (ctx₀ ≤ v_fd₀)

@[qualif]
def Le1 (ctx₀ : Int) (v_fd₀ : Int) : Prop :=
  (ctx₀ ≤ (v_fd₀ - 1))

end WrappersWasiFdAdviseQualifs

open WrappersWasiFdAdviseQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiFdAdvise_proof : WrappersWasiFdAdvise := by
  unfold WrappersWasiFdAdvise
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

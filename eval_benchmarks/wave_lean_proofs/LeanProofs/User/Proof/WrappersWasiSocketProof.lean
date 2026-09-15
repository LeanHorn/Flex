import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiSocket
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiSocketQualifs

@[qualif]
def EqTrue (domain₀ : Prop) : Prop :=
  domain₀

@[qualif]
def EqFalse (domain₀ : Prop) : Prop :=
  (¬domain₀)

@[qualif]
def EqZero (domain₀ : Int) : Prop :=
  (domain₀ = 0)

@[qualif]
def GtZero (domain₀ : Int) : Prop :=
  (domain₀ > 0)

@[qualif]
def GeZero (domain₀ : Int) : Prop :=
  (domain₀ ≥ 0)

@[qualif]
def LtZero (domain₀ : Int) : Prop :=
  (domain₀ < 0)

@[qualif]
def LeZero (domain₀ : Int) : Prop :=
  (domain₀ ≤ 0)

@[qualif]
def Eq (domain₀ : Int) (ty₀ : Int) : Prop :=
  (domain₀ = ty₀)

@[qualif]
def Gt (domain₀ : Int) (ty₀ : Int) : Prop :=
  (domain₀ > ty₀)

@[qualif]
def Ge (domain₀ : Int) (ty₀ : Int) : Prop :=
  (domain₀ ≥ ty₀)

@[qualif]
def Lt (domain₀ : Int) (ty₀ : Int) : Prop :=
  (domain₀ < ty₀)

@[qualif]
def Le (domain₀ : Int) (ty₀ : Int) : Prop :=
  (domain₀ ≤ ty₀)

@[qualif]
def Le1 (domain₀ : Int) (ty₀ : Int) : Prop :=
  (domain₀ ≤ (ty₀ - 1))

end WrappersWasiSocketQualifs

open WrappersWasiSocketQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiSocket_proof : WrappersWasiSocket := by
  unfold WrappersWasiSocket
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

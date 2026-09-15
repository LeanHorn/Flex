import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FftDoit
open Classical
set_option linter.unusedVariables false


namespace F

namespace FftDoitQualifs

@[qualif]
def EqTrue (i₀ : Prop) : Prop :=
  i₀

@[qualif]
def EqFalse (i₀ : Prop) : Prop :=
  (¬i₀)

@[qualif]
def EqZero (i₀ : Int) : Prop :=
  (i₀ = 0)

@[qualif]
def GtZero (i₀ : Int) : Prop :=
  (i₀ > 0)

@[qualif]
def GeZero (i₀ : Int) : Prop :=
  (i₀ ≥ 0)

@[qualif]
def LtZero (i₀ : Int) : Prop :=
  (i₀ < 0)

@[qualif]
def LeZero (i₀ : Int) : Prop :=
  (i₀ ≤ 0)

@[qualif]
def Eq (i₀ : Int) (np₀ : Int) : Prop :=
  (i₀ = np₀)

@[qualif]
def Gt (i₀ : Int) (np₀ : Int) : Prop :=
  (i₀ > np₀)

@[qualif]
def Ge (i₀ : Int) (np₀ : Int) : Prop :=
  (i₀ ≥ np₀)

@[qualif]
def Lt (i₀ : Int) (np₀ : Int) : Prop :=
  (i₀ < np₀)

@[qualif]
def Le (i₀ : Int) (np₀ : Int) : Prop :=
  (i₀ ≤ np₀)

@[qualif]
def Le1 (i₀ : Int) (np₀ : Int) : Prop :=
  (i₀ ≤ (np₀ - 1))

end FftDoitQualifs

open FftDoitQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def FftDoit_proof : FftDoit := by
  unfold FftDoit
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

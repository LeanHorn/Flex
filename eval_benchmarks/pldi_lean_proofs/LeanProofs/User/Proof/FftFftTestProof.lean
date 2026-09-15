import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FftFftTest
open Classical
set_option linter.unusedVariables false


namespace F

namespace FftFftTestQualifs

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
def Eq (i₀ : Int) (_kr₀ : Int) : Prop :=
  (i₀ = _kr₀)

@[qualif]
def Gt (i₀ : Int) (_kr₀ : Int) : Prop :=
  (i₀ > _kr₀)

@[qualif]
def Ge (i₀ : Int) (_kr₀ : Int) : Prop :=
  (i₀ ≥ _kr₀)

@[qualif]
def Lt (i₀ : Int) (_kr₀ : Int) : Prop :=
  (i₀ < _kr₀)

@[qualif]
def Le (i₀ : Int) (_kr₀ : Int) : Prop :=
  (i₀ ≤ _kr₀)

@[qualif]
def Le1 (i₀ : Int) (_kr₀ : Int) : Prop :=
  (i₀ ≤ (_kr₀ - 1))

end FftFftTestQualifs

open FftFftTestQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def FftFftTest_proof : FftFftTest := by
  unfold FftFftTest
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

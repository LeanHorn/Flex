import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FftLoopB
open Classical
set_option linter.unusedVariables false


namespace F

namespace FftLoopBQualifs

@[qualif]
def EqTrue (is₀ : Prop) : Prop :=
  is₀

@[qualif]
def EqFalse (is₀ : Prop) : Prop :=
  (¬is₀)

@[qualif]
def EqZero (is₀ : Int) : Prop :=
  (is₀ = 0)

@[qualif]
def GtZero (is₀ : Int) : Prop :=
  (is₀ > 0)

@[qualif]
def GeZero (is₀ : Int) : Prop :=
  (is₀ ≥ 0)

@[qualif]
def LtZero (is₀ : Int) : Prop :=
  (is₀ < 0)

@[qualif]
def LeZero (is₀ : Int) : Prop :=
  (is₀ ≤ 0)

@[qualif]
def Eq (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ = id₀)

@[qualif]
def Gt (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ > id₀)

@[qualif]
def Ge (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ ≥ id₀)

@[qualif]
def Lt (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ < id₀)

@[qualif]
def Le (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ ≤ id₀)

@[qualif]
def Le1 (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ ≤ (id₀ - 1))

end FftLoopBQualifs

open FftLoopBQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def FftLoopB_proof : FftLoopB := by
  unfold FftLoopB
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

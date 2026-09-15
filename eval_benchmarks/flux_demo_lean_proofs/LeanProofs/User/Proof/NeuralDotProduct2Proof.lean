import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NeuralDotProduct2
open Classical
set_option linter.unusedVariables false


namespace F

namespace NeuralDotProduct2Qualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ = item₀)

@[qualif]
def Gt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ > item₀)

@[qualif]
def Ge (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≥ item₀)

@[qualif]
def Lt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ < item₀)

@[qualif]
def Le (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ item₀)

@[qualif]
def Le1 (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ (item₀ - 1))

end NeuralDotProduct2Qualifs

open NeuralDotProduct2Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def NeuralDotProduct2_proof : NeuralDotProduct2 := by
  unfold NeuralDotProduct2
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

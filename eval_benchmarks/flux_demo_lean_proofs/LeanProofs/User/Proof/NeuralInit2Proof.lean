import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NeuralInit2
open Classical
set_option linter.unusedVariables false


namespace F

namespace NeuralInit2Qualifs

@[qualif]
def EqTrue (f₀ : Prop) : Prop :=
  f₀

@[qualif]
def EqFalse (f₀ : Prop) : Prop :=
  (¬f₀)

@[qualif]
def EqZero (f₀ : Int) : Prop :=
  (f₀ = 0)

@[qualif]
def GtZero (f₀ : Int) : Prop :=
  (f₀ > 0)

@[qualif]
def GeZero (f₀ : Int) : Prop :=
  (f₀ ≥ 0)

@[qualif]
def LtZero (f₀ : Int) : Prop :=
  (f₀ < 0)

@[qualif]
def LeZero (f₀ : Int) : Prop :=
  (f₀ ≤ 0)

@[qualif]
def Eq (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ = a'₁)

@[qualif]
def Gt (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ > a'₁)

@[qualif]
def Ge (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ ≥ a'₁)

@[qualif]
def Lt (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ < a'₁)

@[qualif]
def Le (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ ≤ a'₁)

@[qualif]
def Le1 (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ ≤ (a'₁ - 1))

end NeuralInit2Qualifs

open NeuralInit2Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def NeuralInit2_proof : NeuralInit2 := by
  unfold NeuralInit2
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

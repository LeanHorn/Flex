import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NeuralInit0
open Classical
set_option linter.unusedVariables false


namespace F

namespace NeuralInit0Qualifs

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
def Eq (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ = f₁)

@[qualif]
def Gt (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ > f₁)

@[qualif]
def Ge (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ ≥ f₁)

@[qualif]
def Lt (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ < f₁)

@[qualif]
def Le (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ ≤ f₁)

@[qualif]
def Le1 (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ ≤ (f₁ - 1))

end NeuralInit0Qualifs

open NeuralInit0Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def NeuralInit0_proof : NeuralInit0 := by
  unfold NeuralInit0
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NeuralImpl__1__Backward
open Classical
set_option linter.unusedVariables false


namespace F

namespace NeuralImpl1BackwardQualifs

@[qualif]
def EqTrue (i₁ : Prop) : Prop :=
  i₁

@[qualif]
def EqFalse (i₁ : Prop) : Prop :=
  (¬i₁)

@[qualif]
def EqZero (i₁ : Int) : Prop :=
  (i₁ = 0)

@[qualif]
def GtZero (i₁ : Int) : Prop :=
  (i₁ > 0)

@[qualif]
def GeZero (i₁ : Int) : Prop :=
  (i₁ ≥ 0)

@[qualif]
def LtZero (i₁ : Int) : Prop :=
  (i₁ < 0)

@[qualif]
def LeZero (i₁ : Int) : Prop :=
  (i₁ ≤ 0)

@[qualif]
def Eq (i₁ : Int) (o₁ : Int) : Prop :=
  (i₁ = o₁)

@[qualif]
def Gt (i₁ : Int) (o₁ : Int) : Prop :=
  (i₁ > o₁)

@[qualif]
def Ge (i₁ : Int) (o₁ : Int) : Prop :=
  (i₁ ≥ o₁)

@[qualif]
def Lt (i₁ : Int) (o₁ : Int) : Prop :=
  (i₁ < o₁)

@[qualif]
def Le (i₁ : Int) (o₁ : Int) : Prop :=
  (i₁ ≤ o₁)

@[qualif]
def Le1 (i₁ : Int) (o₁ : Int) : Prop :=
  (i₁ ≤ (o₁ - 1))

end NeuralImpl1BackwardQualifs

open NeuralImpl1BackwardQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def NeuralImpl__1__Backward_proof : NeuralImpl__1__Backward := by
  unfold NeuralImpl__1__Backward
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

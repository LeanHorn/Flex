import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NeuralImpl__1__New
open Classical
set_option linter.unusedVariables false


namespace F

namespace NeuralImpl1NewQualifs

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
def Eq (a'₀ : Int) (hidden_sizes_elem₀ : Int) : Prop :=
  (a'₀ = hidden_sizes_elem₀)

@[qualif]
def Gt (a'₀ : Int) (hidden_sizes_elem₀ : Int) : Prop :=
  (a'₀ > hidden_sizes_elem₀)

@[qualif]
def Ge (a'₀ : Int) (hidden_sizes_elem₀ : Int) : Prop :=
  (a'₀ ≥ hidden_sizes_elem₀)

@[qualif]
def Lt (a'₀ : Int) (hidden_sizes_elem₀ : Int) : Prop :=
  (a'₀ < hidden_sizes_elem₀)

@[qualif]
def Le (a'₀ : Int) (hidden_sizes_elem₀ : Int) : Prop :=
  (a'₀ ≤ hidden_sizes_elem₀)

@[qualif]
def Le1 (a'₀ : Int) (hidden_sizes_elem₀ : Int) : Prop :=
  (a'₀ ≤ (hidden_sizes_elem₀ - 1))

end NeuralImpl1NewQualifs

open NeuralImpl1NewQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def NeuralImpl__1__New_proof : NeuralImpl__1__New := by
  unfold NeuralImpl__1__New
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

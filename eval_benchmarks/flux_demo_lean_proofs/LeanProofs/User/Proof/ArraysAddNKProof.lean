import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.ArraysAddNK
open Classical
set_option linter.unusedVariables false


namespace F

namespace ArraysAddNKQualifs

@[qualif]
def EqTrue (k₀ : Prop) : Prop :=
  k₀

@[qualif]
def EqFalse (k₀ : Prop) : Prop :=
  (¬k₀)

@[qualif]
def EqZero (k₀ : Int) : Prop :=
  (k₀ = 0)

@[qualif]
def GtZero (k₀ : Int) : Prop :=
  (k₀ > 0)

@[qualif]
def GeZero (k₀ : Int) : Prop :=
  (k₀ ≥ 0)

@[qualif]
def LtZero (k₀ : Int) : Prop :=
  (k₀ < 0)

@[qualif]
def LeZero (k₀ : Int) : Prop :=
  (k₀ ≤ 0)

@[qualif]
def Eq (k₀ : Int) (k₁ : Int) : Prop :=
  (k₀ = k₁)

@[qualif]
def Gt (k₀ : Int) (k₁ : Int) : Prop :=
  (k₀ > k₁)

@[qualif]
def Ge (k₀ : Int) (k₁ : Int) : Prop :=
  (k₀ ≥ k₁)

@[qualif]
def Lt (k₀ : Int) (k₁ : Int) : Prop :=
  (k₀ < k₁)

@[qualif]
def Le (k₀ : Int) (k₁ : Int) : Prop :=
  (k₀ ≤ k₁)

@[qualif]
def Le1 (k₀ : Int) (k₁ : Int) : Prop :=
  (k₀ ≤ (k₁ - 1))

end ArraysAddNKQualifs

open ArraysAddNKQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def ArraysAddNK_proof : ArraysAddNK := by
  unfold ArraysAddNK
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

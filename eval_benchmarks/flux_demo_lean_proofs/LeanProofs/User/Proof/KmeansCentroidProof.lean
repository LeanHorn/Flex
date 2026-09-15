import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.KmeansCentroid
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmeansCentroidQualifs

@[qualif]
def EqTrue (this₀ : Prop) : Prop :=
  this₀

@[qualif]
def EqFalse (this₀ : Prop) : Prop :=
  (¬this₀)

@[qualif]
def EqZero (this₀ : Int) : Prop :=
  (this₀ = 0)

@[qualif]
def GtZero (this₀ : Int) : Prop :=
  (this₀ > 0)

@[qualif]
def GeZero (this₀ : Int) : Prop :=
  (this₀ ≥ 0)

@[qualif]
def LtZero (this₀ : Int) : Prop :=
  (this₀ < 0)

@[qualif]
def LeZero (this₀ : Int) : Prop :=
  (this₀ ≤ 0)

@[qualif]
def Eq (this₀ : Int) (this₁ : Int) : Prop :=
  (this₀ = this₁)

@[qualif]
def Gt (this₀ : Int) (this₁ : Int) : Prop :=
  (this₀ > this₁)

@[qualif]
def Ge (this₀ : Int) (this₁ : Int) : Prop :=
  (this₀ ≥ this₁)

@[qualif]
def Lt (this₀ : Int) (this₁ : Int) : Prop :=
  (this₀ < this₁)

@[qualif]
def Le (this₀ : Int) (this₁ : Int) : Prop :=
  (this₀ ≤ this₁)

@[qualif]
def Le1 (this₀ : Int) (this₁ : Int) : Prop :=
  (this₀ ≤ (this₁ - 1))

end KmeansCentroidQualifs

open KmeansCentroidQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def KmeansCentroid_proof : KmeansCentroid := by
  unfold KmeansCentroid
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

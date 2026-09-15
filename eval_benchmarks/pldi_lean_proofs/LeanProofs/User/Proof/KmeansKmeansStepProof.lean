import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.KmeansKmeansStep
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmeansKmeansStepQualifs

@[qualif]
def EqTrue (ps₀ : Prop) : Prop :=
  ps₀

@[qualif]
def EqFalse (ps₀ : Prop) : Prop :=
  (¬ps₀)

@[qualif]
def EqZero (ps₀ : Int) : Prop :=
  (ps₀ = 0)

@[qualif]
def GtZero (ps₀ : Int) : Prop :=
  (ps₀ > 0)

@[qualif]
def GeZero (ps₀ : Int) : Prop :=
  (ps₀ ≥ 0)

@[qualif]
def LtZero (ps₀ : Int) : Prop :=
  (ps₀ < 0)

@[qualif]
def LeZero (ps₀ : Int) : Prop :=
  (ps₀ ≤ 0)

@[qualif]
def Eq (ps₀ : Int) (a'₁ : Int) : Prop :=
  (ps₀ = a'₁)

@[qualif]
def Gt (ps₀ : Int) (a'₁ : Int) : Prop :=
  (ps₀ > a'₁)

@[qualif]
def Ge (ps₀ : Int) (a'₁ : Int) : Prop :=
  (ps₀ ≥ a'₁)

@[qualif]
def Lt (ps₀ : Int) (a'₁ : Int) : Prop :=
  (ps₀ < a'₁)

@[qualif]
def Le (ps₀ : Int) (a'₁ : Int) : Prop :=
  (ps₀ ≤ a'₁)

@[qualif]
def Le1 (ps₀ : Int) (a'₁ : Int) : Prop :=
  (ps₀ ≤ (a'₁ - 1))

end KmeansKmeansStepQualifs

open KmeansKmeansStepQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def KmeansKmeansStep_proof : KmeansKmeansStep := by
  unfold KmeansKmeansStep
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

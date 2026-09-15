import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SimplexUnb1
open Classical
set_option linter.unusedVariables false


namespace F

namespace SimplexUnb1Qualifs

@[qualif]
def EqTrue (j₀ : Prop) : Prop :=
  j₀

@[qualif]
def EqFalse (j₀ : Prop) : Prop :=
  (¬j₀)

@[qualif]
def EqZero (j₀ : Int) : Prop :=
  (j₀ = 0)

@[qualif]
def GtZero (j₀ : Int) : Prop :=
  (j₀ > 0)

@[qualif]
def GeZero (j₀ : Int) : Prop :=
  (j₀ ≥ 0)

@[qualif]
def LtZero (j₀ : Int) : Prop :=
  (j₀ < 0)

@[qualif]
def LeZero (j₀ : Int) : Prop :=
  (j₀ ≤ 0)

@[qualif]
def Eq (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ = a'₁)

@[qualif]
def Gt (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ > a'₁)

@[qualif]
def Ge (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ ≥ a'₁)

@[qualif]
def Lt (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ < a'₁)

@[qualif]
def Le (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ ≤ a'₁)

@[qualif]
def Le1 (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ ≤ (a'₁ - 1))

end SimplexUnb1Qualifs

open SimplexUnb1Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def SimplexUnb1_proof : SimplexUnb1 := by
  unfold SimplexUnb1
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

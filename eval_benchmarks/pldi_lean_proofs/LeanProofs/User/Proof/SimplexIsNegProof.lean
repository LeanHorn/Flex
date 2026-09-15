import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SimplexIsNeg
open Classical
set_option linter.unusedVariables false


namespace F

namespace SimplexIsNegQualifs

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

end SimplexIsNegQualifs

open SimplexIsNegQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def SimplexIsNeg_proof : SimplexIsNeg := by
  unfold SimplexIsNeg
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

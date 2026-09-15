import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SimplexEnterVar
open Classical
set_option linter.unusedVariables false


namespace F

namespace SimplexEnterVarQualifs

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
def Eq (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ = j_₀)

@[qualif]
def Gt (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ > j_₀)

@[qualif]
def Ge (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ ≥ j_₀)

@[qualif]
def Lt (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ < j_₀)

@[qualif]
def Le (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ ≤ j_₀)

@[qualif]
def Le1 (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ ≤ (j_₀ - 1))

end SimplexEnterVarQualifs

open SimplexEnterVarQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def SimplexEnterVar_proof : SimplexEnterVar := by
  unfold SimplexEnterVar
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

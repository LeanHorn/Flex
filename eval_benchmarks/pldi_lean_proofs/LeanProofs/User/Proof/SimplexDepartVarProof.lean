import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SimplexDepartVar
open Classical
set_option linter.unusedVariables false


namespace F

namespace SimplexDepartVarQualifs

@[qualif]
def EqTrue (i₀ : Prop) : Prop :=
  i₀

@[qualif]
def EqFalse (i₀ : Prop) : Prop :=
  (¬i₀)

@[qualif]
def EqZero (i₀ : Int) : Prop :=
  (i₀ = 0)

@[qualif]
def GtZero (i₀ : Int) : Prop :=
  (i₀ > 0)

@[qualif]
def GeZero (i₀ : Int) : Prop :=
  (i₀ ≥ 0)

@[qualif]
def LtZero (i₀ : Int) : Prop :=
  (i₀ < 0)

@[qualif]
def LeZero (i₀ : Int) : Prop :=
  (i₀ ≤ 0)

@[qualif]
def Eq (i₀ : Int) (i_₀ : Int) : Prop :=
  (i₀ = i_₀)

@[qualif]
def Gt (i₀ : Int) (i_₀ : Int) : Prop :=
  (i₀ > i_₀)

@[qualif]
def Ge (i₀ : Int) (i_₀ : Int) : Prop :=
  (i₀ ≥ i_₀)

@[qualif]
def Lt (i₀ : Int) (i_₀ : Int) : Prop :=
  (i₀ < i_₀)

@[qualif]
def Le (i₀ : Int) (i_₀ : Int) : Prop :=
  (i₀ ≤ i_₀)

@[qualif]
def Le1 (i₀ : Int) (i_₀ : Int) : Prop :=
  (i₀ ≤ (i_₀ - 1))

end SimplexDepartVarQualifs

open SimplexDepartVarQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def SimplexDepartVar_proof : SimplexDepartVar := by
  unfold SimplexDepartVar
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

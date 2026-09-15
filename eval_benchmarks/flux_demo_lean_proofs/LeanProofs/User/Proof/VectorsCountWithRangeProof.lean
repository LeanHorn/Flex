import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VectorsCountWithRange
open Classical
set_option linter.unusedVariables false


namespace F

namespace VectorsCountWithRangeQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (iter₀ : Int) : Prop :=
  (v₀ = iter₀)

@[qualif]
def Gt (v₀ : Int) (iter₀ : Int) : Prop :=
  (v₀ > iter₀)

@[qualif]
def Ge (v₀ : Int) (iter₀ : Int) : Prop :=
  (v₀ ≥ iter₀)

@[qualif]
def Lt (v₀ : Int) (iter₀ : Int) : Prop :=
  (v₀ < iter₀)

@[qualif]
def Le (v₀ : Int) (iter₀ : Int) : Prop :=
  (v₀ ≤ iter₀)

@[qualif]
def Le1 (v₀ : Int) (iter₀ : Int) : Prop :=
  (v₀ ≤ (iter₀ - 1))

end VectorsCountWithRangeQualifs

open VectorsCountWithRangeQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VectorsCountWithRange_proof : VectorsCountWithRange := by
  unfold VectorsCountWithRange
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

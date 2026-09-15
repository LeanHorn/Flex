import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.HeapsortHeapSort
open Classical
set_option linter.unusedVariables false


namespace F

namespace HeapsortHeapSortQualifs

@[qualif]
def EqTrue (start₀ : Prop) : Prop :=
  start₀

@[qualif]
def EqFalse (start₀ : Prop) : Prop :=
  (¬start₀)

@[qualif]
def EqZero (start₀ : Int) : Prop :=
  (start₀ = 0)

@[qualif]
def GtZero (start₀ : Int) : Prop :=
  (start₀ > 0)

@[qualif]
def GeZero (start₀ : Int) : Prop :=
  (start₀ ≥ 0)

@[qualif]
def LtZero (start₀ : Int) : Prop :=
  (start₀ < 0)

@[qualif]
def LeZero (start₀ : Int) : Prop :=
  (start₀ ≤ 0)

@[qualif]
def Eq (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ = end₀)

@[qualif]
def Gt (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ > end₀)

@[qualif]
def Ge (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ ≥ end₀)

@[qualif]
def Lt (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ < end₀)

@[qualif]
def Le (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ ≤ end₀)

@[qualif]
def Le1 (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ ≤ (end₀ - 1))

end HeapsortHeapSortQualifs

open HeapsortHeapSortQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def HeapsortHeapSort_proof : HeapsortHeapSort := by
  unfold HeapsortHeapSort
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BsearchBinarySearch
open Classical
set_option linter.unusedVariables false


namespace F

namespace BsearchBinarySearchQualifs

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
def Eq (k₀ : Int) (items₀ : Int) : Prop :=
  (k₀ = items₀)

@[qualif]
def Gt (k₀ : Int) (items₀ : Int) : Prop :=
  (k₀ > items₀)

@[qualif]
def Ge (k₀ : Int) (items₀ : Int) : Prop :=
  (k₀ ≥ items₀)

@[qualif]
def Lt (k₀ : Int) (items₀ : Int) : Prop :=
  (k₀ < items₀)

@[qualif]
def Le (k₀ : Int) (items₀ : Int) : Prop :=
  (k₀ ≤ items₀)

@[qualif]
def Le1 (k₀ : Int) (items₀ : Int) : Prop :=
  (k₀ ≤ (items₀ - 1))

end BsearchBinarySearchQualifs

open BsearchBinarySearchQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def BsearchBinarySearch_proof : BsearchBinarySearch := by
  unfold BsearchBinarySearch
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

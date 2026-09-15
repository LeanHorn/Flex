import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.ArraysAdd2N
open Classical
set_option linter.unusedVariables false


namespace F

namespace ArraysAdd2NQualifs

@[qualif]
def EqTrue (arr_elem₀ : Prop) : Prop :=
  arr_elem₀

@[qualif]
def EqFalse (arr_elem₀ : Prop) : Prop :=
  (¬arr_elem₀)

@[qualif]
def EqZero (arr_elem₀ : Int) : Prop :=
  (arr_elem₀ = 0)

@[qualif]
def GtZero (arr_elem₀ : Int) : Prop :=
  (arr_elem₀ > 0)

@[qualif]
def GeZero (arr_elem₀ : Int) : Prop :=
  (arr_elem₀ ≥ 0)

@[qualif]
def LtZero (arr_elem₀ : Int) : Prop :=
  (arr_elem₀ < 0)

@[qualif]
def LeZero (arr_elem₀ : Int) : Prop :=
  (arr_elem₀ ≤ 0)

@[qualif]
def Eq (arr_elem₀ : Int) (res₀ : Int) : Prop :=
  (arr_elem₀ = res₀)

@[qualif]
def Gt (arr_elem₀ : Int) (res₀ : Int) : Prop :=
  (arr_elem₀ > res₀)

@[qualif]
def Ge (arr_elem₀ : Int) (res₀ : Int) : Prop :=
  (arr_elem₀ ≥ res₀)

@[qualif]
def Lt (arr_elem₀ : Int) (res₀ : Int) : Prop :=
  (arr_elem₀ < res₀)

@[qualif]
def Le (arr_elem₀ : Int) (res₀ : Int) : Prop :=
  (arr_elem₀ ≤ res₀)

@[qualif]
def Le1 (arr_elem₀ : Int) (res₀ : Int) : Prop :=
  (arr_elem₀ ≤ (res₀ - 1))

end ArraysAdd2NQualifs

open ArraysAdd2NQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def ArraysAdd2N_proof : ArraysAdd2N := by
  unfold ArraysAdd2N
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

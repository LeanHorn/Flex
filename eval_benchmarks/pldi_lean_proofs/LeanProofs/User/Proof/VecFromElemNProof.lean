import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecFromElemN
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecFromElemNQualifs

@[qualif]
def EqTrue (elem₀ : Prop) : Prop :=
  elem₀

@[qualif]
def EqFalse (elem₀ : Prop) : Prop :=
  (¬elem₀)

@[qualif]
def EqZero (elem₀ : Int) : Prop :=
  (elem₀ = 0)

@[qualif]
def GtZero (elem₀ : Int) : Prop :=
  (elem₀ > 0)

@[qualif]
def GeZero (elem₀ : Int) : Prop :=
  (elem₀ ≥ 0)

@[qualif]
def LtZero (elem₀ : Int) : Prop :=
  (elem₀ < 0)

@[qualif]
def LeZero (elem₀ : Int) : Prop :=
  (elem₀ ≤ 0)

@[qualif]
def Eq (elem₀ : Int) (vec₀ : Int) : Prop :=
  (elem₀ = vec₀)

@[qualif]
def Gt (elem₀ : Int) (vec₀ : Int) : Prop :=
  (elem₀ > vec₀)

@[qualif]
def Ge (elem₀ : Int) (vec₀ : Int) : Prop :=
  (elem₀ ≥ vec₀)

@[qualif]
def Lt (elem₀ : Int) (vec₀ : Int) : Prop :=
  (elem₀ < vec₀)

@[qualif]
def Le (elem₀ : Int) (vec₀ : Int) : Prop :=
  (elem₀ ≤ vec₀)

@[qualif]
def Le1 (elem₀ : Int) (vec₀ : Int) : Prop :=
  (elem₀ ≤ (vec₀ - 1))

end VecFromElemNQualifs

open VecFromElemNQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecFromElemN_proof : VecFromElemN := by
  unfold VecFromElemN
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

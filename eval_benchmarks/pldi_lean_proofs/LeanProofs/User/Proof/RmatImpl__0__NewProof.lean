import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RmatImpl__0__New
open Classical
set_option linter.unusedVariables false


namespace F

namespace RmatImpl0NewQualifs

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
def Eq (elem₀ : Int) (inner₀ : Int) : Prop :=
  (elem₀ = inner₀)

@[qualif]
def Gt (elem₀ : Int) (inner₀ : Int) : Prop :=
  (elem₀ > inner₀)

@[qualif]
def Ge (elem₀ : Int) (inner₀ : Int) : Prop :=
  (elem₀ ≥ inner₀)

@[qualif]
def Lt (elem₀ : Int) (inner₀ : Int) : Prop :=
  (elem₀ < inner₀)

@[qualif]
def Le (elem₀ : Int) (inner₀ : Int) : Prop :=
  (elem₀ ≤ inner₀)

@[qualif]
def Le1 (elem₀ : Int) (inner₀ : Int) : Prop :=
  (elem₀ ≤ (inner₀ - 1))

end RmatImpl0NewQualifs

open RmatImpl0NewQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RmatImpl__0__New_proof : RmatImpl__0__New := by
  unfold RmatImpl__0__New
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

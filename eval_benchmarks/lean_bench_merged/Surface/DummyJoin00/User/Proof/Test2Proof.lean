import Flex
import Surface.DummyJoin00.Flux.Prelude
import Surface.DummyJoin00.Flux.VC.Test2
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test2Qualifs

@[qualif]
def EqTrue (x₀ : Prop) : Prop :=
  x₀

@[qualif]
def EqFalse (x₀ : Prop) : Prop :=
  (¬x₀)

@[qualif]
def EqZero (x₀ : Int) : Prop :=
  (x₀ = 0)

@[qualif]
def GtZero (x₀ : Int) : Prop :=
  (x₀ > 0)

@[qualif]
def GeZero (x₀ : Int) : Prop :=
  (x₀ ≥ 0)

@[qualif]
def LtZero (x₀ : Int) : Prop :=
  (x₀ < 0)

@[qualif]
def LeZero (x₀ : Int) : Prop :=
  (x₀ ≤ 0)

@[qualif]
def Eq (x₀ : Int) (res₀ : Int) : Prop :=
  (x₀ = res₀)

@[qualif]
def Gt (x₀ : Int) (res₀ : Int) : Prop :=
  (x₀ > res₀)

@[qualif]
def Ge (x₀ : Int) (res₀ : Int) : Prop :=
  (x₀ ≥ res₀)

@[qualif]
def Lt (x₀ : Int) (res₀ : Int) : Prop :=
  (x₀ < res₀)

@[qualif]
def Le (x₀ : Int) (res₀ : Int) : Prop :=
  (x₀ ≤ res₀)

@[qualif]
def Le1 (x₀ : Int) (res₀ : Int) : Prop :=
  (x₀ ≤ (res₀ - 1))

end Test2Qualifs

open Test2Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def Test2_proof : Test2 := by
  unfold Test2
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

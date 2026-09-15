import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.HeapsortShiftDown
open Classical
set_option linter.unusedVariables false


namespace F

namespace HeapsortShiftDownQualifs

@[qualif]
def EqTrue (root₀ : Prop) : Prop :=
  root₀

@[qualif]
def EqFalse (root₀ : Prop) : Prop :=
  (¬root₀)

@[qualif]
def EqZero (root₀ : Int) : Prop :=
  (root₀ = 0)

@[qualif]
def GtZero (root₀ : Int) : Prop :=
  (root₀ > 0)

@[qualif]
def GeZero (root₀ : Int) : Prop :=
  (root₀ ≥ 0)

@[qualif]
def LtZero (root₀ : Int) : Prop :=
  (root₀ < 0)

@[qualif]
def LeZero (root₀ : Int) : Prop :=
  (root₀ ≤ 0)

@[qualif]
def Eq (root₀ : Int) (a'₁ : Int) : Prop :=
  (root₀ = a'₁)

@[qualif]
def Gt (root₀ : Int) (a'₁ : Int) : Prop :=
  (root₀ > a'₁)

@[qualif]
def Ge (root₀ : Int) (a'₁ : Int) : Prop :=
  (root₀ ≥ a'₁)

@[qualif]
def Lt (root₀ : Int) (a'₁ : Int) : Prop :=
  (root₀ < a'₁)

@[qualif]
def Le (root₀ : Int) (a'₁ : Int) : Prop :=
  (root₀ ≤ a'₁)

@[qualif]
def Le1 (root₀ : Int) (a'₁ : Int) : Prop :=
  (root₀ ≤ (a'₁ - 1))

end HeapsortShiftDownQualifs

open HeapsortShiftDownQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def HeapsortShiftDown_proof : HeapsortShiftDown := by
  unfold HeapsortShiftDown
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

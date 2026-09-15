import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.DotproductDot4
open Classical
set_option linter.unusedVariables false


namespace F

namespace DotproductDot4Qualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ = item₀)

@[qualif]
def Gt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ > item₀)

@[qualif]
def Ge (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≥ item₀)

@[qualif]
def Lt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ < item₀)

@[qualif]
def Le (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ item₀)

@[qualif]
def Le1 (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ (item₀ - 1))

end DotproductDot4Qualifs

open DotproductDot4Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def DotproductDot4_proof : DotproductDot4 := by
  unfold DotproductDot4
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

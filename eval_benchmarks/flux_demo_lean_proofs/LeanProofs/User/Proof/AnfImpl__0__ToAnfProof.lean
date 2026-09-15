import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.AnfImpl__0__ToAnf
open Classical
set_option linter.unusedVariables false


namespace F

namespace AnfImpl0ToAnfQualifs

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
def Eq (a'₀ : Int) (count₀ : Int) : Prop :=
  (a'₀ = count₀)

@[qualif]
def Gt (a'₀ : Int) (count₀ : Int) : Prop :=
  (a'₀ > count₀)

@[qualif]
def Ge (a'₀ : Int) (count₀ : Int) : Prop :=
  (a'₀ ≥ count₀)

@[qualif]
def Lt (a'₀ : Int) (count₀ : Int) : Prop :=
  (a'₀ < count₀)

@[qualif]
def Le (a'₀ : Int) (count₀ : Int) : Prop :=
  (a'₀ ≤ count₀)

@[qualif]
def Le1 (a'₀ : Int) (count₀ : Int) : Prop :=
  (a'₀ ≤ (count₀ - 1))

end AnfImpl0ToAnfQualifs

open AnfImpl0ToAnfQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def AnfImpl__0__ToAnf_proof : AnfImpl__0__ToAnf := by
  unfold AnfImpl__0__ToAnf
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

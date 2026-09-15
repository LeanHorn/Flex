import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VecDequeImpl__3__Reserve
open Classical
set_option linter.unusedVariables false


namespace F

namespace VecDequeImpl3ReserveQualifs

@[qualif]
def EqTrue (additional₀ : Prop) : Prop :=
  additional₀

@[qualif]
def EqFalse (additional₀ : Prop) : Prop :=
  (¬additional₀)

@[qualif]
def EqZero (additional₀ : Int) : Prop :=
  (additional₀ = 0)

@[qualif]
def GtZero (additional₀ : Int) : Prop :=
  (additional₀ > 0)

@[qualif]
def GeZero (additional₀ : Int) : Prop :=
  (additional₀ ≥ 0)

@[qualif]
def LtZero (additional₀ : Int) : Prop :=
  (additional₀ < 0)

@[qualif]
def LeZero (additional₀ : Int) : Prop :=
  (additional₀ ≤ 0)

@[qualif]
def Eq (additional₀ : Int) (old_cap₀ : Int) : Prop :=
  (additional₀ = old_cap₀)

@[qualif]
def Gt (additional₀ : Int) (old_cap₀ : Int) : Prop :=
  (additional₀ > old_cap₀)

@[qualif]
def Ge (additional₀ : Int) (old_cap₀ : Int) : Prop :=
  (additional₀ ≥ old_cap₀)

@[qualif]
def Lt (additional₀ : Int) (old_cap₀ : Int) : Prop :=
  (additional₀ < old_cap₀)

@[qualif]
def Le (additional₀ : Int) (old_cap₀ : Int) : Prop :=
  (additional₀ ≤ old_cap₀)

@[qualif]
def Le1 (additional₀ : Int) (old_cap₀ : Int) : Prop :=
  (additional₀ ≤ (old_cap₀ - 1))

end VecDequeImpl3ReserveQualifs

open VecDequeImpl3ReserveQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def VecDequeImpl__3__Reserve_proof : VecDequeImpl__3__Reserve := by
  unfold VecDequeImpl__3__Reserve
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RuntimeImpl__0__ReadU32Pair
open Classical
set_option linter.unusedVariables false


namespace F

namespace RuntimeImpl0ReadU32PairQualifs

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
def Eq (a'₀ : Int) (start₀ : Int) : Prop :=
  (a'₀ = start₀)

@[qualif]
def Gt (a'₀ : Int) (start₀ : Int) : Prop :=
  (a'₀ > start₀)

@[qualif]
def Ge (a'₀ : Int) (start₀ : Int) : Prop :=
  (a'₀ ≥ start₀)

@[qualif]
def Lt (a'₀ : Int) (start₀ : Int) : Prop :=
  (a'₀ < start₀)

@[qualif]
def Le (a'₀ : Int) (start₀ : Int) : Prop :=
  (a'₀ ≤ start₀)

@[qualif]
def Le1 (a'₀ : Int) (start₀ : Int) : Prop :=
  (a'₀ ≤ (start₀ - 1))

end RuntimeImpl0ReadU32PairQualifs

open RuntimeImpl0ReadU32PairQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RuntimeImpl__0__ReadU32Pair_proof : RuntimeImpl__0__ReadU32Pair := by
  unfold RuntimeImpl__0__ReadU32Pair
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

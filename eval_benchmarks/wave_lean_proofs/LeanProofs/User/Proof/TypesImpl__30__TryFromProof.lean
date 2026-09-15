import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TypesImpl__30__TryFrom
open Classical
set_option linter.unusedVariables false


namespace F

namespace TypesImpl30TryFromQualifs

@[qualif]
def EqTrue (flags₀ : Prop) : Prop :=
  flags₀

@[qualif]
def EqFalse (flags₀ : Prop) : Prop :=
  (¬flags₀)

@[qualif]
def EqZero (flags₀ : Int) : Prop :=
  (flags₀ = 0)

@[qualif]
def GtZero (flags₀ : Int) : Prop :=
  (flags₀ > 0)

@[qualif]
def GeZero (flags₀ : Int) : Prop :=
  (flags₀ ≥ 0)

@[qualif]
def LtZero (flags₀ : Int) : Prop :=
  (flags₀ < 0)

@[qualif]
def LeZero (flags₀ : Int) : Prop :=
  (flags₀ ≤ 0)

@[qualif]
def Eq (flags₀ : Int) (a'₁ : Int) : Prop :=
  (flags₀ = a'₁)

@[qualif]
def Gt (flags₀ : Int) (a'₁ : Int) : Prop :=
  (flags₀ > a'₁)

@[qualif]
def Ge (flags₀ : Int) (a'₁ : Int) : Prop :=
  (flags₀ ≥ a'₁)

@[qualif]
def Lt (flags₀ : Int) (a'₁ : Int) : Prop :=
  (flags₀ < a'₁)

@[qualif]
def Le (flags₀ : Int) (a'₁ : Int) : Prop :=
  (flags₀ ≤ a'₁)

@[qualif]
def Le1 (flags₀ : Int) (a'₁ : Int) : Prop :=
  (flags₀ ≤ (a'₁ - 1))

end TypesImpl30TryFromQualifs

open TypesImpl30TryFromQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def TypesImpl__30__TryFrom_proof : TypesImpl__30__TryFrom := by
  unfold TypesImpl__30__TryFrom
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

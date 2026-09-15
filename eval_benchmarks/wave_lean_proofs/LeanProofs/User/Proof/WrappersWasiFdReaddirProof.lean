import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiFdReaddir
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiFdReaddirQualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (n₁ : Int) : Prop :=
  (n₀ = n₁)

@[qualif]
def Gt (n₀ : Int) (n₁ : Int) : Prop :=
  (n₀ > n₁)

@[qualif]
def Ge (n₀ : Int) (n₁ : Int) : Prop :=
  (n₀ ≥ n₁)

@[qualif]
def Lt (n₀ : Int) (n₁ : Int) : Prop :=
  (n₀ < n₁)

@[qualif]
def Le (n₀ : Int) (n₁ : Int) : Prop :=
  (n₀ ≤ n₁)

@[qualif]
def Le1 (n₀ : Int) (n₁ : Int) : Prop :=
  (n₀ ≤ (n₁ - 1))

end WrappersWasiFdReaddirQualifs

open WrappersWasiFdReaddirQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiFdReaddir_proof : WrappersWasiFdReaddir := by
  unfold WrappersWasiFdReaddir
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

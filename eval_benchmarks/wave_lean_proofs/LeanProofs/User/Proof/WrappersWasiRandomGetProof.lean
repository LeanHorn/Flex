import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiRandomGet
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiRandomGetQualifs

@[qualif]
def EqTrue (ptr₀ : Prop) : Prop :=
  ptr₀

@[qualif]
def EqFalse (ptr₀ : Prop) : Prop :=
  (¬ptr₀)

@[qualif]
def EqZero (ptr₀ : Int) : Prop :=
  (ptr₀ = 0)

@[qualif]
def GtZero (ptr₀ : Int) : Prop :=
  (ptr₀ > 0)

@[qualif]
def GeZero (ptr₀ : Int) : Prop :=
  (ptr₀ ≥ 0)

@[qualif]
def LtZero (ptr₀ : Int) : Prop :=
  (ptr₀ < 0)

@[qualif]
def LeZero (ptr₀ : Int) : Prop :=
  (ptr₀ ≤ 0)

@[qualif]
def Eq (ptr₀ : Int) (len₀ : Int) : Prop :=
  (ptr₀ = len₀)

@[qualif]
def Gt (ptr₀ : Int) (len₀ : Int) : Prop :=
  (ptr₀ > len₀)

@[qualif]
def Ge (ptr₀ : Int) (len₀ : Int) : Prop :=
  (ptr₀ ≥ len₀)

@[qualif]
def Lt (ptr₀ : Int) (len₀ : Int) : Prop :=
  (ptr₀ < len₀)

@[qualif]
def Le (ptr₀ : Int) (len₀ : Int) : Prop :=
  (ptr₀ ≤ len₀)

@[qualif]
def Le1 (ptr₀ : Int) (len₀ : Int) : Prop :=
  (ptr₀ ≤ (len₀ - 1))

end WrappersWasiRandomGetQualifs

open WrappersWasiRandomGetQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiRandomGet_proof : WrappersWasiRandomGet := by
  unfold WrappersWasiRandomGet
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

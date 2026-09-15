import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.OsTracePread
open Classical
set_option linter.unusedVariables false


namespace F

namespace OsTracePreadQualifs

@[qualif]
def EqTrue (cnt₀ : Prop) : Prop :=
  cnt₀

@[qualif]
def EqFalse (cnt₀ : Prop) : Prop :=
  (¬cnt₀)

@[qualif]
def EqZero (cnt₀ : Int) : Prop :=
  (cnt₀ = 0)

@[qualif]
def GtZero (cnt₀ : Int) : Prop :=
  (cnt₀ > 0)

@[qualif]
def GeZero (cnt₀ : Int) : Prop :=
  (cnt₀ ≥ 0)

@[qualif]
def LtZero (cnt₀ : Int) : Prop :=
  (cnt₀ < 0)

@[qualif]
def LeZero (cnt₀ : Int) : Prop :=
  (cnt₀ ≤ 0)

@[qualif]
def Eq (cnt₀ : Int) (fd₀ : Int) : Prop :=
  (cnt₀ = fd₀)

@[qualif]
def Gt (cnt₀ : Int) (fd₀ : Int) : Prop :=
  (cnt₀ > fd₀)

@[qualif]
def Ge (cnt₀ : Int) (fd₀ : Int) : Prop :=
  (cnt₀ ≥ fd₀)

@[qualif]
def Lt (cnt₀ : Int) (fd₀ : Int) : Prop :=
  (cnt₀ < fd₀)

@[qualif]
def Le (cnt₀ : Int) (fd₀ : Int) : Prop :=
  (cnt₀ ≤ fd₀)

@[qualif]
def Le1 (cnt₀ : Int) (fd₀ : Int) : Prop :=
  (cnt₀ ≤ (fd₀ - 1))

end OsTracePreadQualifs

open OsTracePreadQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def OsTracePread_proof : OsTracePread := by
  unfold OsTracePread
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

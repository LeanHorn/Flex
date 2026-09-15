import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.OsTraceReadlinkat
open Classical
set_option linter.unusedVariables false


namespace F

namespace OsTraceReadlinkatQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (cnt₀ : Int) : Prop :=
  (v₀ = cnt₀)

@[qualif]
def Gt (v₀ : Int) (cnt₀ : Int) : Prop :=
  (v₀ > cnt₀)

@[qualif]
def Ge (v₀ : Int) (cnt₀ : Int) : Prop :=
  (v₀ ≥ cnt₀)

@[qualif]
def Lt (v₀ : Int) (cnt₀ : Int) : Prop :=
  (v₀ < cnt₀)

@[qualif]
def Le (v₀ : Int) (cnt₀ : Int) : Prop :=
  (v₀ ≤ cnt₀)

@[qualif]
def Le1 (v₀ : Int) (cnt₀ : Int) : Prop :=
  (v₀ ≤ (cnt₀ - 1))

end OsTraceReadlinkatQualifs

open OsTraceReadlinkatQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def OsTraceReadlinkat_proof : OsTraceReadlinkat := by
  unfold OsTraceReadlinkat
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

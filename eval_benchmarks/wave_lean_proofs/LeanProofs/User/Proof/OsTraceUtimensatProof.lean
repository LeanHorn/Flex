import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.OsTraceUtimensat
open Classical
set_option linter.unusedVariables false


namespace F

namespace OsTraceUtimensatQualifs

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
def Eq (v₀ : Int) (len₀ : Int) : Prop :=
  (v₀ = len₀)

@[qualif]
def Gt (v₀ : Int) (len₀ : Int) : Prop :=
  (v₀ > len₀)

@[qualif]
def Ge (v₀ : Int) (len₀ : Int) : Prop :=
  (v₀ ≥ len₀)

@[qualif]
def Lt (v₀ : Int) (len₀ : Int) : Prop :=
  (v₀ < len₀)

@[qualif]
def Le (v₀ : Int) (len₀ : Int) : Prop :=
  (v₀ ≤ len₀)

@[qualif]
def Le1 (v₀ : Int) (len₀ : Int) : Prop :=
  (v₀ ≤ (len₀ - 1))

end OsTraceUtimensatQualifs

open OsTraceUtimensatQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def OsTraceUtimensat_proof : OsTraceUtimensat := by
  unfold OsTraceUtimensat
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

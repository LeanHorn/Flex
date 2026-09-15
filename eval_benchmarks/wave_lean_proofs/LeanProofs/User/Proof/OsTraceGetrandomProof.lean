import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.OsTraceGetrandom
open Classical
set_option linter.unusedVariables false


namespace F

namespace OsTraceGetrandomQualifs

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
def Eq (cnt₀ : Int) (flags₀ : Int) : Prop :=
  (cnt₀ = flags₀)

@[qualif]
def Gt (cnt₀ : Int) (flags₀ : Int) : Prop :=
  (cnt₀ > flags₀)

@[qualif]
def Ge (cnt₀ : Int) (flags₀ : Int) : Prop :=
  (cnt₀ ≥ flags₀)

@[qualif]
def Lt (cnt₀ : Int) (flags₀ : Int) : Prop :=
  (cnt₀ < flags₀)

@[qualif]
def Le (cnt₀ : Int) (flags₀ : Int) : Prop :=
  (cnt₀ ≤ flags₀)

@[qualif]
def Le1 (cnt₀ : Int) (flags₀ : Int) : Prop :=
  (cnt₀ ≤ (flags₀ - 1))

end OsTraceGetrandomQualifs

open OsTraceGetrandomQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def OsTraceGetrandom_proof : OsTraceGetrandom := by
  unfold OsTraceGetrandom
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TypesPlatformImpl__3__Parse
open Classical
set_option linter.unusedVariables false


namespace F

namespace TypesPlatformImpl3ParseQualifs

@[qualif]
def EqTrue (host_buf₀ : Prop) : Prop :=
  host_buf₀

@[qualif]
def EqFalse (host_buf₀ : Prop) : Prop :=
  (¬host_buf₀)

@[qualif]
def EqZero (host_buf₀ : Int) : Prop :=
  (host_buf₀ = 0)

@[qualif]
def GtZero (host_buf₀ : Int) : Prop :=
  (host_buf₀ > 0)

@[qualif]
def GeZero (host_buf₀ : Int) : Prop :=
  (host_buf₀ ≥ 0)

@[qualif]
def LtZero (host_buf₀ : Int) : Prop :=
  (host_buf₀ < 0)

@[qualif]
def LeZero (host_buf₀ : Int) : Prop :=
  (host_buf₀ ≤ 0)

@[qualif]
def Eq (host_buf₀ : Int) (in_idx₀ : Int) : Prop :=
  (host_buf₀ = in_idx₀)

@[qualif]
def Gt (host_buf₀ : Int) (in_idx₀ : Int) : Prop :=
  (host_buf₀ > in_idx₀)

@[qualif]
def Ge (host_buf₀ : Int) (in_idx₀ : Int) : Prop :=
  (host_buf₀ ≥ in_idx₀)

@[qualif]
def Lt (host_buf₀ : Int) (in_idx₀ : Int) : Prop :=
  (host_buf₀ < in_idx₀)

@[qualif]
def Le (host_buf₀ : Int) (in_idx₀ : Int) : Prop :=
  (host_buf₀ ≤ in_idx₀)

@[qualif]
def Le1 (host_buf₀ : Int) (in_idx₀ : Int) : Prop :=
  (host_buf₀ ≤ (in_idx₀ - 1))

end TypesPlatformImpl3ParseQualifs

open TypesPlatformImpl3ParseQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def TypesPlatformImpl__3__Parse_proof : TypesPlatformImpl__3__Parse := by
  unfold TypesPlatformImpl__3__Parse
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

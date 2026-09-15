import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.PathResolutionResolvePath
open Classical
set_option linter.unusedVariables false


namespace F

namespace PathResolutionResolvePathQualifs

@[qualif]
def EqTrue (path₀ : Prop) : Prop :=
  path₀

@[qualif]
def EqFalse (path₀ : Prop) : Prop :=
  (¬path₀)

@[qualif]
def EqZero (path₀ : Int) : Prop :=
  (path₀ = 0)

@[qualif]
def GtZero (path₀ : Int) : Prop :=
  (path₀ > 0)

@[qualif]
def GeZero (path₀ : Int) : Prop :=
  (path₀ ≥ 0)

@[qualif]
def LtZero (path₀ : Int) : Prop :=
  (path₀ < 0)

@[qualif]
def LeZero (path₀ : Int) : Prop :=
  (path₀ ≤ 0)

@[qualif]
def Eq (path₀ : Int) (dirfd₀ : Int) : Prop :=
  (path₀ = dirfd₀)

@[qualif]
def Gt (path₀ : Int) (dirfd₀ : Int) : Prop :=
  (path₀ > dirfd₀)

@[qualif]
def Ge (path₀ : Int) (dirfd₀ : Int) : Prop :=
  (path₀ ≥ dirfd₀)

@[qualif]
def Lt (path₀ : Int) (dirfd₀ : Int) : Prop :=
  (path₀ < dirfd₀)

@[qualif]
def Le (path₀ : Int) (dirfd₀ : Int) : Prop :=
  (path₀ ≤ dirfd₀)

@[qualif]
def Le1 (path₀ : Int) (dirfd₀ : Int) : Prop :=
  (path₀ ≤ (dirfd₀ - 1))

end PathResolutionResolvePathQualifs

open PathResolutionResolvePathQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def PathResolutionResolvePath_proof : PathResolutionResolvePath := by
  unfold PathResolutionResolvePath
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

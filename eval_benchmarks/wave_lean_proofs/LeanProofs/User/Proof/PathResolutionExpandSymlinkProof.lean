import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.PathResolutionExpandSymlink
open Classical
set_option linter.unusedVariables false


namespace F

namespace PathResolutionExpandSymlinkQualifs

@[qualif]
def EqTrue (linkpath_components₀ : Prop) : Prop :=
  linkpath_components₀

@[qualif]
def EqFalse (linkpath_components₀ : Prop) : Prop :=
  (¬linkpath_components₀)

@[qualif]
def EqZero (linkpath_components₀ : Int) : Prop :=
  (linkpath_components₀ = 0)

@[qualif]
def GtZero (linkpath_components₀ : Int) : Prop :=
  (linkpath_components₀ > 0)

@[qualif]
def GeZero (linkpath_components₀ : Int) : Prop :=
  (linkpath_components₀ ≥ 0)

@[qualif]
def LtZero (linkpath_components₀ : Int) : Prop :=
  (linkpath_components₀ < 0)

@[qualif]
def LeZero (linkpath_components₀ : Int) : Prop :=
  (linkpath_components₀ ≤ 0)

@[qualif]
def Eq (linkpath_components₀ : Int) (dirfd₀ : Int) : Prop :=
  (linkpath_components₀ = dirfd₀)

@[qualif]
def Gt (linkpath_components₀ : Int) (dirfd₀ : Int) : Prop :=
  (linkpath_components₀ > dirfd₀)

@[qualif]
def Ge (linkpath_components₀ : Int) (dirfd₀ : Int) : Prop :=
  (linkpath_components₀ ≥ dirfd₀)

@[qualif]
def Lt (linkpath_components₀ : Int) (dirfd₀ : Int) : Prop :=
  (linkpath_components₀ < dirfd₀)

@[qualif]
def Le (linkpath_components₀ : Int) (dirfd₀ : Int) : Prop :=
  (linkpath_components₀ ≤ dirfd₀)

@[qualif]
def Le1 (linkpath_components₀ : Int) (dirfd₀ : Int) : Prop :=
  (linkpath_components₀ ≤ (dirfd₀ - 1))

end PathResolutionExpandSymlinkQualifs

open PathResolutionExpandSymlinkQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def PathResolutionExpandSymlink_proof : PathResolutionExpandSymlink := by
  unfold PathResolutionExpandSymlink
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

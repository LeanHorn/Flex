import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.PathResolutionExpandPath
open Classical
set_option linter.unusedVariables false


namespace F

namespace PathResolutionExpandPathQualifs

@[qualif]
def EqTrue (vec₀ : Prop) : Prop :=
  vec₀

@[qualif]
def EqFalse (vec₀ : Prop) : Prop :=
  (¬vec₀)

@[qualif]
def EqZero (vec₀ : Int) : Prop :=
  (vec₀ = 0)

@[qualif]
def GtZero (vec₀ : Int) : Prop :=
  (vec₀ > 0)

@[qualif]
def GeZero (vec₀ : Int) : Prop :=
  (vec₀ ≥ 0)

@[qualif]
def LtZero (vec₀ : Int) : Prop :=
  (vec₀ < 0)

@[qualif]
def LeZero (vec₀ : Int) : Prop :=
  (vec₀ ≤ 0)

@[qualif]
def Eq (vec₀ : Int) (dirfd₀ : Int) : Prop :=
  (vec₀ = dirfd₀)

@[qualif]
def Gt (vec₀ : Int) (dirfd₀ : Int) : Prop :=
  (vec₀ > dirfd₀)

@[qualif]
def Ge (vec₀ : Int) (dirfd₀ : Int) : Prop :=
  (vec₀ ≥ dirfd₀)

@[qualif]
def Lt (vec₀ : Int) (dirfd₀ : Int) : Prop :=
  (vec₀ < dirfd₀)

@[qualif]
def Le (vec₀ : Int) (dirfd₀ : Int) : Prop :=
  (vec₀ ≤ dirfd₀)

@[qualif]
def Le1 (vec₀ : Int) (dirfd₀ : Int) : Prop :=
  (vec₀ ≤ (dirfd₀ - 1))

end PathResolutionExpandPathQualifs

open PathResolutionExpandPathQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def PathResolutionExpandPath_proof : PathResolutionExpandPath := by
  unfold PathResolutionExpandPath
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

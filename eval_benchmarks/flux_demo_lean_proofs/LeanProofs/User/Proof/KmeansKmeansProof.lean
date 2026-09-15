import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.KmeansKmeans
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmeansKmeansQualifs

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
def Eq (v₀ : Int) (points₀ : Int) : Prop :=
  (v₀ = points₀)

@[qualif]
def Gt (v₀ : Int) (points₀ : Int) : Prop :=
  (v₀ > points₀)

@[qualif]
def Ge (v₀ : Int) (points₀ : Int) : Prop :=
  (v₀ ≥ points₀)

@[qualif]
def Lt (v₀ : Int) (points₀ : Int) : Prop :=
  (v₀ < points₀)

@[qualif]
def Le (v₀ : Int) (points₀ : Int) : Prop :=
  (v₀ ≤ points₀)

@[qualif]
def Le1 (v₀ : Int) (points₀ : Int) : Prop :=
  (v₀ ≤ (points₀ - 1))

end KmeansKmeansQualifs

open KmeansKmeansQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def KmeansKmeans_proof : KmeansKmeans := by
  unfold KmeansKmeans
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

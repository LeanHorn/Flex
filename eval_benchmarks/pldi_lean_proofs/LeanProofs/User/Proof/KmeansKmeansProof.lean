import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.KmeansKmeans
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmeansKmeansQualifs

@[qualif]
def EqTrue (ps₀ : Prop) : Prop :=
  ps₀

@[qualif]
def EqFalse (ps₀ : Prop) : Prop :=
  (¬ps₀)

@[qualif]
def EqZero (ps₀ : Int) : Prop :=
  (ps₀ = 0)

@[qualif]
def GtZero (ps₀ : Int) : Prop :=
  (ps₀ > 0)

@[qualif]
def GeZero (ps₀ : Int) : Prop :=
  (ps₀ ≥ 0)

@[qualif]
def LtZero (ps₀ : Int) : Prop :=
  (ps₀ < 0)

@[qualif]
def LeZero (ps₀ : Int) : Prop :=
  (ps₀ ≤ 0)

@[qualif]
def Eq (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ = iters₀)

@[qualif]
def Gt (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ > iters₀)

@[qualif]
def Ge (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ ≥ iters₀)

@[qualif]
def Lt (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ < iters₀)

@[qualif]
def Le (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ ≤ iters₀)

@[qualif]
def Le1 (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ ≤ (iters₀ - 1))

end KmeansKmeansQualifs

open KmeansKmeansQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def KmeansKmeans_proof : KmeansKmeans := by
  unfold KmeansKmeans
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiEnvironGet
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiEnvironGetQualifs

@[qualif]
def EqTrue (env₀ : Prop) : Prop :=
  env₀

@[qualif]
def EqFalse (env₀ : Prop) : Prop :=
  (¬env₀)

@[qualif]
def EqZero (env₀ : Int) : Prop :=
  (env₀ = 0)

@[qualif]
def GtZero (env₀ : Int) : Prop :=
  (env₀ > 0)

@[qualif]
def GeZero (env₀ : Int) : Prop :=
  (env₀ ≥ 0)

@[qualif]
def LtZero (env₀ : Int) : Prop :=
  (env₀ < 0)

@[qualif]
def LeZero (env₀ : Int) : Prop :=
  (env₀ ≤ 0)

@[qualif]
def Eq (env₀ : Int) (env_buf₀ : Int) : Prop :=
  (env₀ = env_buf₀)

@[qualif]
def Gt (env₀ : Int) (env_buf₀ : Int) : Prop :=
  (env₀ > env_buf₀)

@[qualif]
def Ge (env₀ : Int) (env_buf₀ : Int) : Prop :=
  (env₀ ≥ env_buf₀)

@[qualif]
def Lt (env₀ : Int) (env_buf₀ : Int) : Prop :=
  (env₀ < env_buf₀)

@[qualif]
def Le (env₀ : Int) (env_buf₀ : Int) : Prop :=
  (env₀ ≤ env_buf₀)

@[qualif]
def Le1 (env₀ : Int) (env_buf₀ : Int) : Prop :=
  (env₀ ≤ (env_buf₀ - 1))

end WrappersWasiEnvironGetQualifs

open WrappersWasiEnvironGetQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiEnvironGet_proof : WrappersWasiEnvironGet := by
  unfold WrappersWasiEnvironGet
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

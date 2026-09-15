import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiArgsGet
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiArgsGetQualifs

@[qualif]
def EqTrue (argv₀ : Prop) : Prop :=
  argv₀

@[qualif]
def EqFalse (argv₀ : Prop) : Prop :=
  (¬argv₀)

@[qualif]
def EqZero (argv₀ : Int) : Prop :=
  (argv₀ = 0)

@[qualif]
def GtZero (argv₀ : Int) : Prop :=
  (argv₀ > 0)

@[qualif]
def GeZero (argv₀ : Int) : Prop :=
  (argv₀ ≥ 0)

@[qualif]
def LtZero (argv₀ : Int) : Prop :=
  (argv₀ < 0)

@[qualif]
def LeZero (argv₀ : Int) : Prop :=
  (argv₀ ≤ 0)

@[qualif]
def Eq (argv₀ : Int) (argv_buf₀ : Int) : Prop :=
  (argv₀ = argv_buf₀)

@[qualif]
def Gt (argv₀ : Int) (argv_buf₀ : Int) : Prop :=
  (argv₀ > argv_buf₀)

@[qualif]
def Ge (argv₀ : Int) (argv_buf₀ : Int) : Prop :=
  (argv₀ ≥ argv_buf₀)

@[qualif]
def Lt (argv₀ : Int) (argv_buf₀ : Int) : Prop :=
  (argv₀ < argv_buf₀)

@[qualif]
def Le (argv₀ : Int) (argv_buf₀ : Int) : Prop :=
  (argv₀ ≤ argv_buf₀)

@[qualif]
def Le1 (argv₀ : Int) (argv_buf₀ : Int) : Prop :=
  (argv₀ ≤ (argv_buf₀ - 1))

end WrappersWasiArgsGetQualifs

open WrappersWasiArgsGetQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiArgsGet_proof : WrappersWasiArgsGet := by
  unfold WrappersWasiArgsGet
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

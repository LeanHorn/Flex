import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiPathOpen
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiPathOpenQualifs

@[qualif]
def EqTrue (v_dir_fd₀ : Prop) : Prop :=
  v_dir_fd₀

@[qualif]
def EqFalse (v_dir_fd₀ : Prop) : Prop :=
  (¬v_dir_fd₀)

@[qualif]
def EqZero (v_dir_fd₀ : Int) : Prop :=
  (v_dir_fd₀ = 0)

@[qualif]
def GtZero (v_dir_fd₀ : Int) : Prop :=
  (v_dir_fd₀ > 0)

@[qualif]
def GeZero (v_dir_fd₀ : Int) : Prop :=
  (v_dir_fd₀ ≥ 0)

@[qualif]
def LtZero (v_dir_fd₀ : Int) : Prop :=
  (v_dir_fd₀ < 0)

@[qualif]
def LeZero (v_dir_fd₀ : Int) : Prop :=
  (v_dir_fd₀ ≤ 0)

@[qualif]
def Eq (v_dir_fd₀ : Int) (dirflags₀ : Int) : Prop :=
  (v_dir_fd₀ = dirflags₀)

@[qualif]
def Gt (v_dir_fd₀ : Int) (dirflags₀ : Int) : Prop :=
  (v_dir_fd₀ > dirflags₀)

@[qualif]
def Ge (v_dir_fd₀ : Int) (dirflags₀ : Int) : Prop :=
  (v_dir_fd₀ ≥ dirflags₀)

@[qualif]
def Lt (v_dir_fd₀ : Int) (dirflags₀ : Int) : Prop :=
  (v_dir_fd₀ < dirflags₀)

@[qualif]
def Le (v_dir_fd₀ : Int) (dirflags₀ : Int) : Prop :=
  (v_dir_fd₀ ≤ dirflags₀)

@[qualif]
def Le1 (v_dir_fd₀ : Int) (dirflags₀ : Int) : Prop :=
  (v_dir_fd₀ ≤ (dirflags₀ - 1))

end WrappersWasiPathOpenQualifs

open WrappersWasiPathOpenQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiPathOpen_proof : WrappersWasiPathOpen := by
  unfold WrappersWasiPathOpen
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

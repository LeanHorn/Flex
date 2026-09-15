import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiSockRecv
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiSockRecvQualifs

@[qualif]
def EqTrue (v_fd₀ : Prop) : Prop :=
  v_fd₀

@[qualif]
def EqFalse (v_fd₀ : Prop) : Prop :=
  (¬v_fd₀)

@[qualif]
def EqZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ = 0)

@[qualif]
def GtZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ > 0)

@[qualif]
def GeZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ ≥ 0)

@[qualif]
def LtZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ < 0)

@[qualif]
def LeZero (v_fd₀ : Int) : Prop :=
  (v_fd₀ ≤ 0)

@[qualif]
def Eq (v_fd₀ : Int) (ri_data₀ : Int) : Prop :=
  (v_fd₀ = ri_data₀)

@[qualif]
def Gt (v_fd₀ : Int) (ri_data₀ : Int) : Prop :=
  (v_fd₀ > ri_data₀)

@[qualif]
def Ge (v_fd₀ : Int) (ri_data₀ : Int) : Prop :=
  (v_fd₀ ≥ ri_data₀)

@[qualif]
def Lt (v_fd₀ : Int) (ri_data₀ : Int) : Prop :=
  (v_fd₀ < ri_data₀)

@[qualif]
def Le (v_fd₀ : Int) (ri_data₀ : Int) : Prop :=
  (v_fd₀ ≤ ri_data₀)

@[qualif]
def Le1 (v_fd₀ : Int) (ri_data₀ : Int) : Prop :=
  (v_fd₀ ≤ (ri_data₀ - 1))

end WrappersWasiSockRecvQualifs

open WrappersWasiSockRecvQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiSockRecv_proof : WrappersWasiSockRecv := by
  unfold WrappersWasiSockRecv
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

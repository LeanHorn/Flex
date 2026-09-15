import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WrappersWasiSockConnect
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrappersWasiSockConnectQualifs

@[qualif]
def EqTrue (sockfd₀ : Prop) : Prop :=
  sockfd₀

@[qualif]
def EqFalse (sockfd₀ : Prop) : Prop :=
  (¬sockfd₀)

@[qualif]
def EqZero (sockfd₀ : Int) : Prop :=
  (sockfd₀ = 0)

@[qualif]
def GtZero (sockfd₀ : Int) : Prop :=
  (sockfd₀ > 0)

@[qualif]
def GeZero (sockfd₀ : Int) : Prop :=
  (sockfd₀ ≥ 0)

@[qualif]
def LtZero (sockfd₀ : Int) : Prop :=
  (sockfd₀ < 0)

@[qualif]
def LeZero (sockfd₀ : Int) : Prop :=
  (sockfd₀ ≤ 0)

@[qualif]
def Eq (sockfd₀ : Int) (addr₀ : Int) : Prop :=
  (sockfd₀ = addr₀)

@[qualif]
def Gt (sockfd₀ : Int) (addr₀ : Int) : Prop :=
  (sockfd₀ > addr₀)

@[qualif]
def Ge (sockfd₀ : Int) (addr₀ : Int) : Prop :=
  (sockfd₀ ≥ addr₀)

@[qualif]
def Lt (sockfd₀ : Int) (addr₀ : Int) : Prop :=
  (sockfd₀ < addr₀)

@[qualif]
def Le (sockfd₀ : Int) (addr₀ : Int) : Prop :=
  (sockfd₀ ≤ addr₀)

@[qualif]
def Le1 (sockfd₀ : Int) (addr₀ : Int) : Prop :=
  (sockfd₀ ≤ (addr₀ - 1))

end WrappersWasiSockConnectQualifs

open WrappersWasiSockConnectQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WrappersWasiSockConnect_proof : WrappersWasiSockConnect := by
  unfold WrappersWasiSockConnect
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FdmapImpl__0__CreateSock
open Classical
set_option linter.unusedVariables false


namespace F

namespace FdmapImpl0CreateSockQualifs

@[qualif]
def EqTrue (k₀ : Prop) : Prop :=
  k₀

@[qualif]
def EqFalse (k₀ : Prop) : Prop :=
  (¬k₀)

@[qualif]
def EqZero (k₀ : Int) : Prop :=
  (k₀ = 0)

@[qualif]
def GtZero (k₀ : Int) : Prop :=
  (k₀ > 0)

@[qualif]
def GeZero (k₀ : Int) : Prop :=
  (k₀ ≥ 0)

@[qualif]
def LtZero (k₀ : Int) : Prop :=
  (k₀ < 0)

@[qualif]
def LeZero (k₀ : Int) : Prop :=
  (k₀ ≤ 0)

@[qualif]
def Eq (k₀ : Int) (self₀ : Int) : Prop :=
  (k₀ = self₀)

@[qualif]
def Gt (k₀ : Int) (self₀ : Int) : Prop :=
  (k₀ > self₀)

@[qualif]
def Ge (k₀ : Int) (self₀ : Int) : Prop :=
  (k₀ ≥ self₀)

@[qualif]
def Lt (k₀ : Int) (self₀ : Int) : Prop :=
  (k₀ < self₀)

@[qualif]
def Le (k₀ : Int) (self₀ : Int) : Prop :=
  (k₀ ≤ self₀)

@[qualif]
def Le1 (k₀ : Int) (self₀ : Int) : Prop :=
  (k₀ ≤ (self₀ - 1))

end FdmapImpl0CreateSockQualifs

open FdmapImpl0CreateSockQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def FdmapImpl__0__CreateSock_proof : FdmapImpl__0__CreateSock := by
  unfold FdmapImpl__0__CreateSock
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

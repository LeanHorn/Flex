import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WritebackWasm2cMarshalAndWritebackU64
open Classical
set_option linter.unusedVariables false


namespace F

namespace WritebackWasm2cMarshalAndWritebackU64Qualifs

@[qualif]
def EqTrue (addr₀ : Prop) : Prop :=
  addr₀

@[qualif]
def EqFalse (addr₀ : Prop) : Prop :=
  (¬addr₀)

@[qualif]
def EqZero (addr₀ : Int) : Prop :=
  (addr₀ = 0)

@[qualif]
def GtZero (addr₀ : Int) : Prop :=
  (addr₀ > 0)

@[qualif]
def GeZero (addr₀ : Int) : Prop :=
  (addr₀ ≥ 0)

@[qualif]
def LtZero (addr₀ : Int) : Prop :=
  (addr₀ < 0)

@[qualif]
def LeZero (addr₀ : Int) : Prop :=
  (addr₀ ≤ 0)

@[qualif]
def Eq (addr₀ : Int) (ctx₀ : Int) : Prop :=
  (addr₀ = ctx₀)

@[qualif]
def Gt (addr₀ : Int) (ctx₀ : Int) : Prop :=
  (addr₀ > ctx₀)

@[qualif]
def Ge (addr₀ : Int) (ctx₀ : Int) : Prop :=
  (addr₀ ≥ ctx₀)

@[qualif]
def Lt (addr₀ : Int) (ctx₀ : Int) : Prop :=
  (addr₀ < ctx₀)

@[qualif]
def Le (addr₀ : Int) (ctx₀ : Int) : Prop :=
  (addr₀ ≤ ctx₀)

@[qualif]
def Le1 (addr₀ : Int) (ctx₀ : Int) : Prop :=
  (addr₀ ≤ (ctx₀ - 1))

end WritebackWasm2cMarshalAndWritebackU64Qualifs

open WritebackWasm2cMarshalAndWritebackU64Qualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WritebackWasm2cMarshalAndWritebackU64_proof : WritebackWasm2cMarshalAndWritebackU64 := by
  unfold WritebackWasm2cMarshalAndWritebackU64
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

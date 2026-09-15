import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WritebackWasm2cMarshalAndWritebackFdstat
open Classical
set_option linter.unusedVariables false


namespace F

namespace WritebackWasm2cMarshalAndWritebackFdstatQualifs

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

end WritebackWasm2cMarshalAndWritebackFdstatQualifs

open WritebackWasm2cMarshalAndWritebackFdstatQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WritebackWasm2cMarshalAndWritebackFdstat_proof : WritebackWasm2cMarshalAndWritebackFdstat := by
  unfold WritebackWasm2cMarshalAndWritebackFdstat
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

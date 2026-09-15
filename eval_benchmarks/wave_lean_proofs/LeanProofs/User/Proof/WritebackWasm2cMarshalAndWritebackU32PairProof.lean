import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WritebackWasm2cMarshalAndWritebackU32Pair
open Classical
set_option linter.unusedVariables false


namespace F

namespace WritebackWasm2cMarshalAndWritebackU32PairQualifs

@[qualif]
def EqTrue (addr0₀ : Prop) : Prop :=
  addr0₀

@[qualif]
def EqFalse (addr0₀ : Prop) : Prop :=
  (¬addr0₀)

@[qualif]
def EqZero (addr0₀ : Int) : Prop :=
  (addr0₀ = 0)

@[qualif]
def GtZero (addr0₀ : Int) : Prop :=
  (addr0₀ > 0)

@[qualif]
def GeZero (addr0₀ : Int) : Prop :=
  (addr0₀ ≥ 0)

@[qualif]
def LtZero (addr0₀ : Int) : Prop :=
  (addr0₀ < 0)

@[qualif]
def LeZero (addr0₀ : Int) : Prop :=
  (addr0₀ ≤ 0)

@[qualif]
def Eq (addr0₀ : Int) (addr1₀ : Int) : Prop :=
  (addr0₀ = addr1₀)

@[qualif]
def Gt (addr0₀ : Int) (addr1₀ : Int) : Prop :=
  (addr0₀ > addr1₀)

@[qualif]
def Ge (addr0₀ : Int) (addr1₀ : Int) : Prop :=
  (addr0₀ ≥ addr1₀)

@[qualif]
def Lt (addr0₀ : Int) (addr1₀ : Int) : Prop :=
  (addr0₀ < addr1₀)

@[qualif]
def Le (addr0₀ : Int) (addr1₀ : Int) : Prop :=
  (addr0₀ ≤ addr1₀)

@[qualif]
def Le1 (addr0₀ : Int) (addr1₀ : Int) : Prop :=
  (addr0₀ ≤ (addr1₀ - 1))

end WritebackWasm2cMarshalAndWritebackU32PairQualifs

open WritebackWasm2cMarshalAndWritebackU32PairQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def WritebackWasm2cMarshalAndWritebackU32Pair_proof : WritebackWasm2cMarshalAndWritebackU32Pair := by
  unfold WritebackWasm2cMarshalAndWritebackU32Pair
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

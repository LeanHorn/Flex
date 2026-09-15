import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TypesImpl__32__Write
open Classical
set_option linter.unusedVariables false


namespace F

namespace TypesImpl32WriteQualifs

@[qualif]
def EqTrue (ptr₀ : Prop) : Prop :=
  ptr₀

@[qualif]
def EqFalse (ptr₀ : Prop) : Prop :=
  (¬ptr₀)

@[qualif]
def EqZero (ptr₀ : Int) : Prop :=
  (ptr₀ = 0)

@[qualif]
def GtZero (ptr₀ : Int) : Prop :=
  (ptr₀ > 0)

@[qualif]
def GeZero (ptr₀ : Int) : Prop :=
  (ptr₀ ≥ 0)

@[qualif]
def LtZero (ptr₀ : Int) : Prop :=
  (ptr₀ < 0)

@[qualif]
def LeZero (ptr₀ : Int) : Prop :=
  (ptr₀ ≤ 0)

@[qualif]
def Eq (ptr₀ : Int) (ctx₀ : Int) : Prop :=
  (ptr₀ = ctx₀)

@[qualif]
def Gt (ptr₀ : Int) (ctx₀ : Int) : Prop :=
  (ptr₀ > ctx₀)

@[qualif]
def Ge (ptr₀ : Int) (ctx₀ : Int) : Prop :=
  (ptr₀ ≥ ctx₀)

@[qualif]
def Lt (ptr₀ : Int) (ctx₀ : Int) : Prop :=
  (ptr₀ < ctx₀)

@[qualif]
def Le (ptr₀ : Int) (ctx₀ : Int) : Prop :=
  (ptr₀ ≤ ctx₀)

@[qualif]
def Le1 (ptr₀ : Int) (ctx₀ : Int) : Prop :=
  (ptr₀ ≤ (ctx₀ - 1))

end TypesImpl32WriteQualifs

open TypesImpl32WriteQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def TypesImpl__32__Write_proof : TypesImpl__32__Write := by
  unfold TypesImpl__32__Write
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

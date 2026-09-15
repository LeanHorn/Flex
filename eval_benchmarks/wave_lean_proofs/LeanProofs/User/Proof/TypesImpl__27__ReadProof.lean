import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TypesImpl__27__Read
open Classical
set_option linter.unusedVariables false


namespace F

namespace TypesImpl27ReadQualifs

@[qualif]
def EqTrue (ctx₀ : Prop) : Prop :=
  ctx₀

@[qualif]
def EqFalse (ctx₀ : Prop) : Prop :=
  (¬ctx₀)

@[qualif]
def EqZero (ctx₀ : Int) : Prop :=
  (ctx₀ = 0)

@[qualif]
def GtZero (ctx₀ : Int) : Prop :=
  (ctx₀ > 0)

@[qualif]
def GeZero (ctx₀ : Int) : Prop :=
  (ctx₀ ≥ 0)

@[qualif]
def LtZero (ctx₀ : Int) : Prop :=
  (ctx₀ < 0)

@[qualif]
def LeZero (ctx₀ : Int) : Prop :=
  (ctx₀ ≤ 0)

@[qualif]
def Eq (ctx₀ : Int) (ptr₀ : Int) : Prop :=
  (ctx₀ = ptr₀)

@[qualif]
def Gt (ctx₀ : Int) (ptr₀ : Int) : Prop :=
  (ctx₀ > ptr₀)

@[qualif]
def Ge (ctx₀ : Int) (ptr₀ : Int) : Prop :=
  (ctx₀ ≥ ptr₀)

@[qualif]
def Lt (ctx₀ : Int) (ptr₀ : Int) : Prop :=
  (ctx₀ < ptr₀)

@[qualif]
def Le (ctx₀ : Int) (ptr₀ : Int) : Prop :=
  (ctx₀ ≤ ptr₀)

@[qualif]
def Le1 (ctx₀ : Int) (ptr₀ : Int) : Prop :=
  (ctx₀ ≤ (ptr₀ - 1))

end TypesImpl27ReadQualifs

open TypesImpl27ReadQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def TypesImpl__27__Read_proof : TypesImpl__27__Read := by
  unfold TypesImpl__27__Read
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

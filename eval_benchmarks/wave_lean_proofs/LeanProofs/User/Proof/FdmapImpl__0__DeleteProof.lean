import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FdmapImpl__0__Delete
open Classical
set_option linter.unusedVariables false


namespace F

namespace FdmapImpl0DeleteQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (self₀ : Int) : Prop :=
  (v₀ = self₀)

@[qualif]
def Gt (v₀ : Int) (self₀ : Int) : Prop :=
  (v₀ > self₀)

@[qualif]
def Ge (v₀ : Int) (self₀ : Int) : Prop :=
  (v₀ ≥ self₀)

@[qualif]
def Lt (v₀ : Int) (self₀ : Int) : Prop :=
  (v₀ < self₀)

@[qualif]
def Le (v₀ : Int) (self₀ : Int) : Prop :=
  (v₀ ≤ self₀)

@[qualif]
def Le1 (v₀ : Int) (self₀ : Int) : Prop :=
  (v₀ ≤ (self₀ - 1))

end FdmapImpl0DeleteQualifs

open FdmapImpl0DeleteQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def FdmapImpl__0__Delete_proof : FdmapImpl__0__Delete := by
  unfold FdmapImpl__0__Delete
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

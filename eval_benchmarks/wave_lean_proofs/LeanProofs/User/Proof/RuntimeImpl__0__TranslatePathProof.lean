import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RuntimeImpl__0__TranslatePath
open Classical
set_option linter.unusedVariables false


namespace F

namespace RuntimeImpl0TranslatePathQualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (path_len₀ : Int) : Prop :=
  (n₀ = path_len₀)

@[qualif]
def Gt (n₀ : Int) (path_len₀ : Int) : Prop :=
  (n₀ > path_len₀)

@[qualif]
def Ge (n₀ : Int) (path_len₀ : Int) : Prop :=
  (n₀ ≥ path_len₀)

@[qualif]
def Lt (n₀ : Int) (path_len₀ : Int) : Prop :=
  (n₀ < path_len₀)

@[qualif]
def Le (n₀ : Int) (path_len₀ : Int) : Prop :=
  (n₀ ≤ path_len₀)

@[qualif]
def Le1 (n₀ : Int) (path_len₀ : Int) : Prop :=
  (n₀ ≤ (path_len₀ - 1))

end RuntimeImpl0TranslatePathQualifs

open RuntimeImpl0TranslatePathQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def RuntimeImpl__0__TranslatePath_proof : RuntimeImpl__0__TranslatePath := by
  unfold RuntimeImpl__0__TranslatePath
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijji
open Classical
set_option linter.unusedVariables false


namespace F

namespace Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijjiQualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ = a'₁)

@[qualif]
def Gt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ > a'₁)

@[qualif]
def Ge (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≥ a'₁)

@[qualif]
def Lt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ < a'₁)

@[qualif]
def Le (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ a'₁)

@[qualif]
def Le1 (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ (a'₁ - 1))

end Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijjiQualifs

open Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijjiQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijji_proof : Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijji := by
  unfold Wasm2cFrontendZWasiSnapshotPreview1ZPathFilestatSetTimesZIiiiijji
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

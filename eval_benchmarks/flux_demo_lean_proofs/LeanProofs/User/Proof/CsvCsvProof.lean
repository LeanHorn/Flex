import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CsvCsv
open Classical
set_option linter.unusedVariables false


namespace F

namespace CsvCsvQualifs

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
def Eq (a'₀ : Int) (row_vals₀ : Int) : Prop :=
  (a'₀ = row_vals₀)

@[qualif]
def Gt (a'₀ : Int) (row_vals₀ : Int) : Prop :=
  (a'₀ > row_vals₀)

@[qualif]
def Ge (a'₀ : Int) (row_vals₀ : Int) : Prop :=
  (a'₀ ≥ row_vals₀)

@[qualif]
def Lt (a'₀ : Int) (row_vals₀ : Int) : Prop :=
  (a'₀ < row_vals₀)

@[qualif]
def Le (a'₀ : Int) (row_vals₀ : Int) : Prop :=
  (a'₀ ≤ row_vals₀)

@[qualif]
def Le1 (a'₀ : Int) (row_vals₀ : Int) : Prop :=
  (a'₀ ≤ (row_vals₀ - 1))

end CsvCsvQualifs

open CsvCsvQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def CsvCsv_proof : CsvCsv := by
  unfold CsvCsv
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

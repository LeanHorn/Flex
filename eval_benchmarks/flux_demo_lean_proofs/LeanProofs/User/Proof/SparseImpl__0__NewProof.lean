import Flex
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SparseImpl__0__New
open Classical
set_option linter.unusedVariables false


namespace F

namespace SparseImpl0NewQualifs

@[qualif]
def EqTrue (nnz₀ : Prop) : Prop :=
  nnz₀

@[qualif]
def EqFalse (nnz₀ : Prop) : Prop :=
  (¬nnz₀)

@[qualif]
def EqZero (nnz₀ : Int) : Prop :=
  (nnz₀ = 0)

@[qualif]
def GtZero (nnz₀ : Int) : Prop :=
  (nnz₀ > 0)

@[qualif]
def GeZero (nnz₀ : Int) : Prop :=
  (nnz₀ ≥ 0)

@[qualif]
def LtZero (nnz₀ : Int) : Prop :=
  (nnz₀ < 0)

@[qualif]
def LeZero (nnz₀ : Int) : Prop :=
  (nnz₀ ≤ 0)

@[qualif]
def Eq (nnz₀ : Int) (col_index₀ : Int) : Prop :=
  (nnz₀ = col_index₀)

@[qualif]
def Gt (nnz₀ : Int) (col_index₀ : Int) : Prop :=
  (nnz₀ > col_index₀)

@[qualif]
def Ge (nnz₀ : Int) (col_index₀ : Int) : Prop :=
  (nnz₀ ≥ col_index₀)

@[qualif]
def Lt (nnz₀ : Int) (col_index₀ : Int) : Prop :=
  (nnz₀ < col_index₀)

@[qualif]
def Le (nnz₀ : Int) (col_index₀ : Int) : Prop :=
  (nnz₀ ≤ col_index₀)

@[qualif]
def Le1 (nnz₀ : Int) (col_index₀ : Int) : Prop :=
  (nnz₀ ≤ (col_index₀ - 1))

end SparseImpl0NewQualifs

open SparseImpl0NewQualifs

set_option maxHeartbeats 5000000
set_option flex.benchPhases true
#time def SparseImpl__0__New_proof : SparseImpl__0__New := by
  unfold SparseImpl__0__New
  (try zap) ; (try benchSimpStar) ; (try solve)

end F

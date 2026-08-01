import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Diagonal operators from summable Hilbert-basis weights

This module constructs the bounded operator

`∑' i, a i • |b i⟩⟨b i|`

from a Hilbert basis `b` and an absolutely summable scalar family `a`. This is the operator-level
foundation needed to build genuine infinite-dimensional Gibbs states from a discrete energy basis,
without representing the generally unbounded Hamiltonian itself as a bounded continuous linear map.
-/

noncomputable section

namespace ContinuousLinearMap.HilbertBasis

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `i`th rank-one term of a diagonal operator in the Hilbert basis `b`. -/
def diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (i : ι) : H →L[ℂ] H :=
  a i • InnerProductSpace.rankOne ℂ (b i) (b i)

/-- Absolute summability of the coefficients implies summability of the diagonal rank-one
operator series in operator norm. -/
theorem summable_diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : Summable (diagonalTerm b a) := by
  refine Summable.of_norm_bounded ha fun i => ?_
  simp [diagonalTerm, norm_smul, b.norm_eq_one]

/-- The bounded diagonal operator with coefficients `a` in the Hilbert basis `b`. -/
def diagonalOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : H →L[ℂ] H :=
  ∑' i, diagonalTerm b a i

/-- The defining diagonal rank-one series converges to `diagonalOp`. -/
theorem hasSum_diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : HasSum (diagonalTerm b a) (diagonalOp b a ha) :=
  (summable_diagonalTerm b a ha).hasSum

end ContinuousLinearMap.HilbertBasis

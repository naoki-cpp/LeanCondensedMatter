import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import LeanCondensedMatter.Analysis.Operator.Compact
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Hilbert-basis diagonal operators

This module constructs the bounded operator

`∑' i, a i • |b i⟩⟨b i|`

from a Hilbert basis `b` and an absolutely summable scalar family `a`. This neutral operator layer
is reused by Fredholm, density-state, and Gibbs constructions. It also records positivity for
summable nonnegative real coefficients, while trace-class and spectral consequences remain downstream.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace HilbertBasis

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `i`th rank-one term of a diagonal operator in the Hilbert basis `b`. -/
def diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (i : ι) : H →L[ℂ] H :=
  a i • InnerProductSpace.rankOne ℂ (b i) (b i)

/-- Absolute summability of the coefficients implies summability of the diagonal rank-one
operator series in operator norm. -/
theorem summable_diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : Summable (diagonalTerm b a) := by
  refine Summable.of_norm_bounded ha fun i => ?_
  simp [diagonalTerm, norm_smul, b.orthonormal.1 i]

/-- The totalized diagonal operator series with coefficients `a` in the Hilbert basis `b`.
Analytic results about its action and compactness state absolute summability explicitly. -/
def diagonalOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ) : H →L[ℂ] H :=
  ∑' i, diagonalTerm b a i

/-- The defining diagonal rank-one series converges to `diagonalOp`. -/
theorem hasSum_diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : HasSum (diagonalTerm b a) (diagonalOp b a) :=
  (summable_diagonalTerm b a ha).hasSum

/-- The diagonal operator acts on each basis vector by its corresponding coefficient. -/
theorem diagonalOp_apply_basis (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (j : ι) :
    diagonalOp b a (b j) = a j • b j := by
  classical
  have hmap := (hasSum_diagonalTerm b a ha).mapL
    (ContinuousLinearMap.apply ℂ H (b j))
  have htsum : (∑' i, diagonalTerm b a i (b j)) = a j • b j := by
    rw [tsum_eq_single j]
    · simp [diagonalTerm, InnerProductSpace.rankOne_apply,
        inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
    · intro i hij
      simp [diagonalTerm, InnerProductSpace.rankOne_apply, b.orthonormal.2 hij]
  calc
    diagonalOp b a (b j) = ∑' i, diagonalTerm b a i (b j) := hmap.tsum_eq.symm
    _ = a j • b j := htsum

/-- A diagonal operator with absolutely summable coefficients is compact. -/
theorem diagonalOp_isCompact (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : IsCompactOperator (diagonalOp b a) := by
  refine isCompactOperator_of_tendsto (hasSum_diagonalTerm b a ha)
    (Filter.Eventually.of_forall fun s : Finset ι => ?_)
  change (∑ i ∈ s, diagonalTerm b a i) ∈ compactOperator (RingHom.id ℂ) H H
  exact Submodule.sum_mem _ fun i _ =>
    (InnerProductSpace.isCompactOperator_rankOne (b i) (b i)).smul (a i)

/-- A diagonal operator with summable real nonnegative coefficients is positive. -/
theorem diagonalOp_isPositive (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    (diagonalOp b (fun i => (a i : ℂ))).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  have hac : Summable fun i => ‖(a i : ℂ)‖ := by simpa using ha
  refine hasSum_le (fun i => ?_)
    (hasSum_zero : HasSum (fun _ : ι => (0 : H →L[ℂ] H)) 0)
    (hasSum_diagonalTerm b (fun i => (a i : ℂ)) hac)
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  have hcoeff : 0 ≤ (a i : ℂ) :=
    (RCLike.ofReal_nonneg (K := ℂ)).mpr (ha_nonneg i)
  simpa [diagonalTerm] using
    (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) (b i)).smul_of_nonneg hcoeff

/-- The lossless diagonal expectation of a positive diagonal operator is its real coefficient. -/
theorem diagonalExpectationValue_diagonalOp (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) (i : ι) :
    ContinuousLinearMap.diagonalExpectationValue
      (diagonalOp b (fun j => (a j : ℂ)))
      (diagonalOp_isPositive b a ha ha_nonneg).isSelfAdjoint (b i) = a i := by
  apply Complex.ofReal_injective
  rw [ContinuousLinearMap.coe_diagonalExpectationValue_right]
  have hac : Summable fun j => ‖(a j : ℂ)‖ := by simpa using ha
  rw [diagonalOp_apply_basis b (fun j => (a j : ℂ)) hac i]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
  simp

/-- `1 + diagonalOp b coeff` acts diagonally with factors `1 + coeff i`. -/
theorem one_add_diagonalOp_apply_basis (b : HilbertBasis ι ℂ H) (coeff : ι → ℂ)
    (hcoeff : Summable fun i => ‖coeff i‖) (i : ι) :
    ((1 : H →L[ℂ] H) + diagonalOp b coeff) (b i) = (1 + coeff i) • b i := by
  change b i + diagonalOp b coeff (b i) = (1 + coeff i) • b i
  rw [diagonalOp_apply_basis b coeff hcoeff i]
  simp [add_smul]

end HilbertBasis

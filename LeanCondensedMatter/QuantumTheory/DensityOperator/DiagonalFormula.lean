import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Diagonal density-state formulas over countable Hilbert bases

When a density operator is diagonal in a Hilbert basis, the canonical expectation is the absolutely
convergent weighted diagonal series. This module also owns the basis-action facts
for density operators constructed from diagonal weights. No finite-dimensional hypothesis is
required.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A real eigenvalue appearing in a diagonalization of a positive density operator is
nonnegative. -/
theorem DensityOperator.diagonal_weight_nonneg (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) (i : ι) :
    0 ≤ w i := by
  have h := ρ.pos.re_inner_nonneg_right (b i)
  rw [hρ i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
  simpa using h

/-- The diagonal expectation series is absolutely summable and has sum equal to the canonical
complex density-state expectation. -/
theorem DensityOperator.hasSum_expectation_diagonal (ρ : DensityOperator H)
    (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    HasSum (fun i => (w i : ℂ) * inner ℂ (b i) (A (b i))) (ρ.expectation A) := by
  have hsum :
      HasSum (fun i => inner ℂ (b i) ((ρ.op * A) (b i))) (ρ.expectation A) := by
    rw [ρ.expectation_apply]
    exact (ρ.isTraceClass.comp_right A).hasSum_trace b
  exact HasSum.congr_fun hsum fun i => by
    symm
    rw [mul_apply_eq_comp]
    calc
      inner ℂ (b i) (ρ.op (A (b i))) =
          inner ℂ (ρ.op (b i)) (A (b i)) := by
        simpa only [ρ.isSelfAdjoint.adjoint_eq] using
          (ContinuousLinearMap.adjoint_inner_right ρ.op (b i) (A (b i)))
      _ = (w i : ℂ) * inner ℂ (b i) (A (b i)) := by
        rw [hρ i, inner_smul_left]
        simp

/-- Dimension-independent diagonal expectation formula over a Hilbert basis. -/
theorem DensityOperator.expectation_eq_tsum_diagonal (ρ : DensityOperator H)
    (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    ρ.expectation A = ∑' i, (w i : ℂ) * inner ℂ (b i) (A (b i)) :=
  (ρ.hasSum_expectation_diagonal A b w hρ).tsum_eq.symm

/-- For an observable, the same diagonal formula is a lossless real-valued series. -/
theorem DensityOperator.hasSum_observableExpectation_diagonal (ρ : DensityOperator H)
    (A : Observable H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    HasSum (fun i => w i * diagonalExpectationValue A.1 A.2 (b i))
      (ρ.observableExpectation A) := by
  have hcomplex :
      HasSum
        (fun i => ((w i * diagonalExpectationValue A.1 A.2 (b i) : ℝ) : ℂ))
        (ρ.expectation A.1) :=
    HasSum.congr_fun (ρ.hasSum_expectation_diagonal A.1 b w hρ) fun i => by
      rw [Complex.ofReal_mul, coe_diagonalExpectationValue_right]
  rw [ρ.expectation_observable A] at hcomplex
  exact Complex.hasSum_ofReal.mp hcomplex

/-- The real-valued observable expectation is the `tsum` of the weighted diagonal values. -/
theorem DensityOperator.observableExpectation_eq_tsum_diagonal (ρ : DensityOperator H)
    (A : Observable H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    ρ.observableExpectation A =
      ∑' i, w i * diagonalExpectationValue A.1 A.2 (b i) :=
  (ρ.hasSum_observableExpectation_diagonal A b w hρ).tsum_eq.symm

/-- If a density operator is diagonal in a Hilbert basis, its weights sum to one. -/
theorem DensityOperator.hasSum_diagonal_weights (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    HasSum w 1 :=
  HasSum.congr_fun (ρ.hasSum_diagonalExpectationValue_eq_one b) fun i => by
    symm
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, happly i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp

/-- Uniformly bounded operator families have continuous density expectations when their diagonal
matrix coefficients are continuous. Operator-norm continuity is not required. -/
theorem DensityOperator.continuous_expectation_of_diagonal
    {T : Type*} [TopologicalSpace T] (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (F : T → (H →L[ℂ] H)) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C)
    (hcoeff : ∀ i, Continuous (fun t => inner ℂ (b i) (F t (b i)))) :
    Continuous (fun t => ρ.expectation (F t)) := by
  have heq : (fun t => ρ.expectation (F t)) =
      (fun t => ∑' i, (w i : ℂ) * inner ℂ (b i) (F t (b i))) :=
    funext fun t => ρ.expectation_eq_tsum_diagonal (F t) b w hρ
  rw [heq]
  apply continuous_tsum (fun i => continuous_const.mul (hcoeff i))
    ((ρ.hasSum_diagonal_weights b w hρ).summable.mul_right C)
  intro i t
  have hw := ρ.diagonal_weight_nonneg b w hρ i
  have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
  have hdiag : ‖inner ℂ (b i) (F t (b i))‖ ≤ C := by
    calc
      _ ≤ ‖b i‖ * ‖F t (b i)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * (‖F t‖ * ‖b i‖) :=
        mul_le_mul_of_nonneg_left ((F t).le_opNorm _) (norm_nonneg _)
      _ ≤ C := by simpa only [hnorm, one_mul, mul_one] using hbound t
  simpa only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw] using
    mul_le_mul_of_nonneg_left hdiag hw

/-- A nonnegative diagonal weight of a density operator is at most one. -/
theorem DensityOperator.diagonal_weight_le_one (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (i : ι) :
    w i ≤ 1 := by
  have hw_nonneg : ∀ j, 0 ≤ w j :=
    ρ.diagonal_weight_nonneg b w happly
  have hs := (ρ.hasSum_diagonal_weights b w happly).summable
  calc
    w i ≤ ∑' j, w j := hs.le_tsum i (fun j _ => hw_nonneg j)
    _ = 1 := (ρ.hasSum_diagonal_weights b w happly).tsum_eq

/-- The normalized diagonal density operator acts by its normalized weight. -/
theorem diagonalDensityOperator_apply_basis (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    (diagonalDensityOperator b a ha ha_nonneg hZ).op (b i) =
      (Real.normalizedWeight a i : ℂ) • b i := by
  change HilbertBasis.diagonalOp b
      (fun i => (Real.normalizedWeight a i : ℂ)) (b i) = _
  simpa using HilbertBasis.diagonalOp_apply_basis b
    (fun i => (Real.normalizedWeight a i : ℂ))
    (by simpa using Real.summable_norm_normalizedWeight a ha) i

end QuantumTheory

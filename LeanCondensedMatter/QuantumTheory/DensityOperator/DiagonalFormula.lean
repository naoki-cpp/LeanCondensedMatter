import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation

/-!
# Diagonal density-state formulas over countable Hilbert bases

When a density operator is diagonal in a Hilbert basis, the canonical expectation is the absolutely
convergent weighted diagonal series. This module also owns the normalization and basis-action facts
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
    rw [ρ.expectation_apply, (ρ.isTraceClass.comp_right A).trace_eq_seriesWrt b]
    exact ((ρ.isTraceClass.comp_right A).summable_traceSeriesWrt b).hasSum
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

/-- Absolute convergence of the diagonal expectation series follows directly from trace-class
closure under bounded right multiplication. -/
theorem DensityOperator.summable_expectation_diagonal (ρ : DensityOperator H)
    (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    Summable (fun i => (w i : ℂ) * inner ℂ (b i) (A (b i))) :=
  (ρ.hasSum_expectation_diagonal A b w hρ).summable

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

/-- The diagonal weights of a density operator are summable. -/
theorem DensityOperator.summable_diagonal_weights (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    Summable w :=
  (ρ.hasSum_diagonal_weights b w happly).summable

/-- A nonnegative diagonal weight of a density operator is at most one. -/
theorem DensityOperator.diagonal_weight_le_one (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (happly : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hw_nonneg : ∀ i, 0 ≤ w i) (i : ι) :
    w i ≤ 1 := by
  have hs := ρ.summable_diagonal_weights b w happly
  calc
    w i ≤ ∑' j, w j := hs.le_tsum i (fun j _ => hw_nonneg j)
    _ = 1 := (ρ.hasSum_diagonal_weights b w happly).tsum_eq

/-- The normalized weight used by `diagonalDensityOperator`. -/
def normalizedDiagonalWeight (a : ι → ℝ) (i : ι) : ℝ :=
  (∑' j, a j)⁻¹ * a i

/-- Absolute summability is preserved by normalization. -/
theorem summable_norm_normalizedDiagonalWeight (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) :
    Summable fun i => ‖normalizedDiagonalWeight a i‖ := by
  have hscaled := ha.mul_left ‖(∑' j, a j)⁻¹‖
  simpa [normalizedDiagonalWeight, norm_mul] using hscaled

/-- The normalized diagonal density operator acts by its normalized weight. -/
theorem diagonalDensityOperator_apply_basis (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    (diagonalDensityOperator b a ha ha_nonneg hZ).op (b i) =
      (normalizedDiagonalWeight a i : ℂ) • b i := by
  change HilbertBasis.diagonalOp b
      (fun i => (normalizedDiagonalWeight a i : ℂ)) (b i) = _
  simpa using HilbertBasis.diagonalOp_apply_basis b
    (fun i => (normalizedDiagonalWeight a i : ℂ))
    (by simpa using summable_norm_normalizedDiagonalWeight a ha) i

/-- Normalized nonnegative weights remain nonnegative. -/
theorem normalizedDiagonalWeight_nonneg (a : ι → ℝ) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    0 ≤ normalizedDiagonalWeight a i :=
  mul_nonneg (inv_nonneg.mpr hZ.le) (ha_nonneg i)

/-- The normalized diagonal weights sum to one. -/
theorem hasSum_normalizedDiagonalWeight (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) :
    HasSum (normalizedDiagonalWeight a) 1 :=
  (diagonalDensityOperator b a ha ha_nonneg hZ).hasSum_diagonal_weights b
    (normalizedDiagonalWeight a) (diagonalDensityOperator_apply_basis b a ha ha_nonneg hZ)

/-- Every normalized diagonal weight is at most one. -/
theorem normalizedDiagonalWeight_le_one (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i)
    (hZ : 0 < ∑' i, a i) (i : ι) :
    normalizedDiagonalWeight a i ≤ 1 :=
  (diagonalDensityOperator b a ha ha_nonneg hZ).diagonal_weight_le_one b
    (normalizedDiagonalWeight a) (diagonalDensityOperator_apply_basis b a ha ha_nonneg hZ)
    (normalizedDiagonalWeight_nonneg a ha_nonneg hZ) i

end QuantumTheory

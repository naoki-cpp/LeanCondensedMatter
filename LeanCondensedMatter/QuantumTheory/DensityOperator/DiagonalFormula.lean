import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation

/-!
# Diagonal expectation formulas over countable Hilbert bases

When a density operator is diagonal in a Hilbert basis, the canonical expectation is the absolutely
convergent weighted diagonal series. No finite-dimensional hypothesis is required. The observable
specialization transports the proved-real series to `ℝ` without defining the physical quantity by
an arbitrary real-part projection.
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

/-- The square-root density operator is diagonal in the same basis, with square-root weights. -/
theorem DensityOperator.sqrtOp_apply_diagonal_basis (ρ : DensityOperator H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) (i : ι) :
    ρ.sqrtOp (b i) = (Real.sqrt (w i) : ℂ) • b i := by
  exact ρ.sqrtOp_apply_eigenvector (by simpa using hρ i)

/-- On a basis diagonalizing the density operator, the Hilbert–Schmidt integrand is exactly the
usual weighted diagonal matrix element. -/
theorem DensityOperator.inner_sqrtOp_comp_apply_eq_diagonal_term
    (ρ : DensityOperator H) (A : H →L[ℂ] H)
    (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) (i : ι) :
    inner ℂ (ρ.sqrtOp (b i)) ((A * ρ.sqrtOp) (b i)) =
      (w i : ℂ) * inner ℂ (b i) (A (b i)) := by
  rw [ρ.sqrtOp_apply_diagonal_basis b w hρ i, mul_apply_eq_comp,
    ρ.sqrtOp_apply_diagonal_basis b w hρ i, map_smul, inner_smul_left,
    inner_smul_right]
  have hsqrt_sq_real : Real.sqrt (w i) * Real.sqrt (w i) = w i := by
    simpa [pow_two] using Real.sq_sqrt (ρ.diagonal_weight_nonneg b w hρ i)
  have hsqrt_sq :
      (Real.sqrt (w i) : ℂ) * (Real.sqrt (w i) : ℂ) = (w i : ℂ) := by
    exact_mod_cast hsqrt_sq_real
  have hstar :
      starRingEnd ℂ (Real.sqrt (w i) : ℂ) = (Real.sqrt (w i) : ℂ) := by
    simp
  rw [hstar, ← mul_assoc, hsqrt_sq]

/-- The diagonal expectation series is absolutely summable and has sum equal to the canonical
complex density-state expectation. -/
theorem DensityOperator.hasSum_expectation_diagonal (ρ : DensityOperator H)
    (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    HasSum (fun i => (w i : ℂ) * inner ℂ (b i) (A (b i))) (ρ.expectation A) := by
  have hsqrt : IsHilbertSchmidt ρ.sqrtOp := ρ.sqrtOp_isHilbertSchmidt
  have hAsqrt : IsHilbertSchmidt (A * ρ.sqrtOp) :=
    isHilbertSchmidt_comp_left A hsqrt
  have hsum :
      HasSum (fun i => inner ℂ (ρ.sqrtOp (b i)) ((A * ρ.sqrtOp) (b i)))
        (innerHS b ρ.sqrtOp (A * ρ.sqrtOp)) :=
    (summable_inner_apply_of_isHilbertSchmidtWrt b
      (hsqrt.isHilbertSchmidtWrt b) (hAsqrt.isHilbertSchmidtWrt b)).hasSum
  have hfunctions :
      (fun i => inner ℂ (ρ.sqrtOp (b i)) ((A * ρ.sqrtOp) (b i))) =
        fun i => (w i : ℂ) * inner ℂ (b i) (A (b i)) := by
    funext i
    exact ρ.inner_sqrtOp_comp_apply_eq_diagonal_term A b w hρ i
  rw [hfunctions] at hsum
  rw [ρ.expectation_eq_innerHS A b]
  exact hsum

/-- Absolute convergence of the diagonal expectation series follows from trace-class density
weights and boundedness of the observed operator, encoded through the Hilbert–Schmidt bridge. -/
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
  have hcomplex := ρ.hasSum_expectation_diagonal A.1 b w hρ
  have hfunctions :
      (fun i => (w i : ℂ) * inner ℂ (b i) (A.1 (b i))) =
        fun i => ((w i * diagonalExpectationValue A.1 A.2 (b i) : ℝ) : ℂ) := by
    funext i
    rw [← coe_diagonalExpectationValue_right A.1 A.2 (b i)]
    norm_cast
  rw [hfunctions, ρ.expectation_observable A] at hcomplex
  have hreal := Complex.reCLM.hasSum hcomplex
  change HasSum (fun i => w i * diagonalExpectationValue A.1 A.2 (b i))
    (ρ.observableExpectation A) at hreal
  exact hreal

/-- The real-valued observable expectation is the `tsum` of the weighted diagonal values. -/
theorem DensityOperator.observableExpectation_eq_tsum_diagonal (ρ : DensityOperator H)
    (A : Observable H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    ρ.observableExpectation A =
      ∑' i, w i * diagonalExpectationValue A.1 A.2 (b i) :=
  (ρ.hasSum_observableExpectation_diagonal A b w hρ).tsum_eq.symm

end QuantumTheory

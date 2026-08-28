import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalPositive

/-!
# Spectral trace of positive diagonal operators

A positive compact operator is spectrally trace-class whenever its lossless diagonal expectation
values against one Hilbert basis are summable. The proof bounds every finite sum of nonzero
eigenvalues by that basis-diagonal sum, using the compact spectral expansion and Parseval. This
criterion packages diagonal operators with summable nonnegative weights as `SpectralTraceClass`
without reindexing repeated eigenspaces.
-/

noncomputable section

namespace ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- A positive compact operator whose lossless diagonal values are summable against one Hilbert
basis has summable nonzero real eigenvalues. -/
theorem hasSummableRealEigenvalues_of_positive_of_summable_diagonal
    (hcompact : IsCompactOperator T) (hpos : T.IsPositive)
    (d : HilbertBasis ι ℂ H)
    (hdiag : Summable fun i => diagonalExpectationValue T hpos.isSelfAdjoint (d i)) :
    HasSummableRealEigenvalues T := by
  classical
  let e : EigenvectorIndex T → H := eigenvectorFamily hcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hcompact hpos.isSymmetric
  have heigen_nonneg (a : EigenvectorIndex T) : 0 ≤ a.1.1 :=
    eigenvalue_nonneg_of_isPositive hpos.toLinearMap a
  rw [HasSummableRealEigenvalues]
  simp_rw [abs_of_nonneg (heigen_nonneg _)]
  refine summable_of_sum_le
    (c := ∑' i, diagonalExpectationValue T hpos.isSelfAdjoint (d i))
    (fun a => heigen_nonneg a) ?_
  intro s
  let f : ι → ℝ := fun i =>
    ∑ a ∈ s, a.1.1 * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2
  have hparseval (a : EigenvectorIndex T) :
      HasSum (fun i => ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2) 1 := by
    have hs := d.hasSum_norm_sq_inner (e a)
    rwa [he.1 a, one_pow] at hs
  have hf_summable : Summable f := by
    unfold f
    exact summable_sum fun a _ => (hparseval a).summable.mul_left a.1.1
  have hf_tsum : ∑' i, f i = ∑ a ∈ s, a.1.1 := by
    unfold f
    rw [Summable.tsum_finsetSum fun a _ => (hparseval a).summable.mul_left a.1.1]
    exact Finset.sum_congr rfl fun a _ => by
      rw [tsum_mul_left, (hparseval a).tsum_eq, mul_one]
  have hf_le (i : ι) : f i ≤ diagonalExpectationValue T hpos.isSelfAdjoint (d i) := by
    have hs := hasSum_eigen_expansion_diagonalExpectationValue
      hcompact hpos.isSelfAdjoint (d i)
    rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum s fun a _ =>
      mul_nonneg (heigen_nonneg a) (sq_nonneg _)
  rw [← hf_tsum]
  exact hf_summable.tsum_le_tsum hf_le hdiag

end ContinuousLinearMap

namespace HilbertBasis

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bundle a diagonal operator with summable nonnegative real weights as spectral-trace-class. -/
theorem diagonalOpSpectralTraceClass (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    SpectralTraceClass (diagonalOp b (fun i => (a i : ℂ))) := by
  let hac : Summable fun i => ‖(a i : ℂ)‖ := by simpa using ha
  let T := diagonalOp b (fun i => (a i : ℂ))
  let hpos : T.IsPositive := diagonalOp_isPositive b a ha ha_nonneg
  have hdiag_point :
      (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (b i)) = a := by
    funext i
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right]
    rw [show T (b i) = a i • b i by
      simpa [T] using diagonalOp_apply_basis b (fun i => (a i : ℂ)) hac i]
    rw [inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hdiag : Summable fun i => diagonalExpectationValue T hpos.isSelfAdjoint (b i) := by
    rw [hdiag_point]
    exact Summable.of_norm ha
  exact SpectralTraceClass.ofPositive
    (diagonalOp_isCompact b (fun i => (a i : ℂ)) hac) hpos
    (hasSummableRealEigenvalues_of_positive_of_summable_diagonal
      (diagonalOp_isCompact b (fun i => (a i : ℂ)) hac) hpos b hdiag)

/-- The spectral trace of a diagonal operator with nonnegative weights is their sum. -/
theorem diagonalOpSpectralTraceClass_trace (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    (diagonalOpSpectralTraceClass b a ha ha_nonneg).trace = ∑' i, a i := by
  let hac : Summable fun i => ‖(a i : ℂ)‖ := by simpa using ha
  let T := diagonalOp b (fun i => (a i : ℂ))
  let hstc := diagonalOpSpectralTraceClass b a ha ha_nonneg
  have htrace := hstc.hasSum_diagonalExpectationValue b
  have hpoint :
      (fun i => diagonalExpectationValue T hstc.isSelfAdjoint (b i)) = a := by
    funext i
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right]
    rw [show T (b i) = a i • b i by
      simpa [T] using diagonalOp_apply_basis b (fun i => (a i : ℂ)) hac i]
    rw [inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  change HasSum (fun i => diagonalExpectationValue T hstc.isSelfAdjoint (b i)) hstc.trace at htrace
  rw [hpoint] at htrace
  exact htrace.tsum_eq.symm

end HilbertBasis

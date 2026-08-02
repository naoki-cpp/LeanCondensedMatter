import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalPositive

/-!
# Spectral trace of positive diagonal operators

A positive compact operator is spectrally trace-class whenever its diagonal against one Hilbert
basis is summable. The proof bounds every finite sum of nonzero eigenvalues by that basis-diagonal
sum, using the compact spectral expansion and Parseval. This criterion packages diagonal operators
with summable nonnegative weights as `SpectralTraceClass` without reindexing repeated eigenspaces.
-/

noncomputable section

namespace ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- A positive compact operator whose diagonal is summable against one Hilbert basis has summable
nonzero real eigenvalues. -/
theorem hasSummableRealEigenvalues_of_positive_of_summable_diagonal
    (hcompact : IsCompactOperator T) (hpos : T.IsPositive)
    (d : HilbertBasis ι ℂ H)
    (hdiag : Summable fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) :
    HasSummableRealEigenvalues T := by
  classical
  let e : EigenvectorIndex T → H := eigenvectorFamily hcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hcompact hpos.isSymmetric
  have heigen_nonneg (a : EigenvectorIndex T) : 0 ≤ a.1.1 :=
    eigenvalue_nonneg_of_isPositive hpos.toLinearMap a
  rw [HasSummableRealEigenvalues]
  simp_rw [abs_of_nonneg (heigen_nonneg _)]
  apply summable_of_sum_le (fun a => heigen_nonneg a)
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
  have hf_le (i : ι) : f i ≤ (inner ℂ (d i) (T (d i)) : ℂ).re := by
    have hs := hasSum_eigen_expansion_inner_apply hcompact hpos.isSymmetric (d i)
    rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum s fun a _ =>
      mul_nonneg (heigen_nonneg a) (sq_nonneg _)
  rw [← hf_tsum]
  exact hf_summable.tsum_le_tsum hf_le hdiag

namespace SpectralTraceClass

/-- Construct spectral-trace data from compactness, positivity, and summability of one Hilbert-basis
diagonal. -/
def ofPositiveSummableDiagonal (hcompact : IsCompactOperator T) (hpos : T.IsPositive)
    (d : HilbertBasis ι ℂ H)
    (hdiag : Summable fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) :
    SpectralTraceClass T :=
  ofPositive hcompact hpos
    (hasSummableRealEigenvalues_of_positive_of_summable_diagonal hcompact hpos d hdiag)

end SpectralTraceClass
end ContinuousLinearMap

namespace HilbertBasis

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bundle a diagonal operator with summable nonnegative real weights as spectral-trace-class. -/
def diagonalOpSpectralTraceClass (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    SpectralTraceClass (diagonalOp b (fun i => (a i : ℂ)) (by simpa using ha)) := by
  let hac : Summable fun i => ‖(a i : ℂ)‖ := by simpa using ha
  let T := diagonalOp b (fun i => (a i : ℂ)) hac
  have hdiag_point :
      (fun i => (inner ℂ (b i) (T (b i)) : ℂ).re) = a := by
    funext i
    rw [show T (b i) = a i • b i by
      simpa [T] using diagonalOp_apply_basis b (fun i => (a i : ℂ)) hac i]
    rw [inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hdiag : Summable fun i => (inner ℂ (b i) (T (b i)) : ℂ).re := by
    rw [hdiag_point]
    exact Summable.of_norm ha
  exact SpectralTraceClass.ofPositiveSummableDiagonal
    (diagonalOp_isCompact b (fun i => (a i : ℂ)) hac)
    (diagonalOp_isPositive b a ha ha_nonneg) b hdiag

/-- The spectral trace of a diagonal operator with nonnegative weights is their sum. -/
theorem diagonalOpSpectralTraceClass_trace (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    (diagonalOpSpectralTraceClass b a ha ha_nonneg).trace = ∑' i, a i := by
  let hac : Summable fun i => ‖(a i : ℂ)‖ := by simpa using ha
  have htrace := (diagonalOpSpectralTraceClass b a ha ha_nonneg).hasSum_inner_apply b
  have hpoint :
      (fun i => (inner ℂ (b i)
        (diagonalOp b (fun i => (a i : ℂ)) hac (b i)) : ℂ).re) = a := by
    funext i
    rw [show diagonalOp b (fun i => (a i : ℂ)) hac (b i) = a i • b i by
      simpa using diagonalOp_apply_basis b (fun i => (a i : ℂ)) hac i]
    rw [inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rw [hpoint] at htrace
  exact htrace.tsum_eq.symm

end HilbertBasis

import LeanCondensedMatter.Analysis.Operator.TraceClass.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Bundled

/-!
# Spectral trace of positive diagonal operators

Absolutely summable nonnegative diagonal weights are trace class in the general operator layer.
Positivity then supplies the self-adjoint spectral specialization and its eigenvalue-sum trace.
-/

noncomputable section

namespace HilbertBasis

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bundle a diagonal operator with summable nonnegative real weights as spectral-trace-class. -/
theorem diagonalOpSpectralTraceClass (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    SpectralTraceClass (diagonalOp b (fun i => (a i : ℂ))) where
  isTraceClass := diagonalOp_isTraceClass b a ha ha_nonneg
  symmetric := (diagonalOp_isPositive b a ha ha_nonneg).isSelfAdjoint.isSymmetric

/-- The spectral trace of a diagonal operator with nonnegative weights is their sum. -/
theorem spectralTrace_diagonalOp_eq_tsum (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    spectralTrace (diagonalOp b (fun i => (a i : ℂ))) = ∑' i, a i := by
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
  change HasSum (fun i => diagonalExpectationValue T hstc.isSelfAdjoint (b i))
    (spectralTrace T) at htrace
  rw [hpoint] at htrace
  exact htrace.tsum_eq.symm

end HilbertBasis

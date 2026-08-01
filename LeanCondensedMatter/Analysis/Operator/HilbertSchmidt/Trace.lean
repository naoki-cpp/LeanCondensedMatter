import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops

/-!
# Reconciling `innerHS` with `spectralTrace`

For a compact self-adjoint spectrally summable operator, the Hilbert–Schmidt inner product against
the identity agrees with its spectral trace.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a compact self-adjoint spectrally summable `A`, `innerHS d 1 A` agrees with the spectral
trace of `A`. -/
theorem innerHS_one_eq_spectralTrace {A : H →L[ℂ] H} (hAcpt : IsCompactOperator A)
    (hAsym : A.IsSymmetric) (hAsum : HasSummableRealEigenvalues A)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    innerHS d 1 A = (spectralTrace hAsum : ℂ) := by
  have hone : (fun i => (inner ℂ ((1 : H →L[ℂ] H) (d i)) (A (d i)) : ℂ)) =
      (fun i => (inner ℂ (d i) (A (d i)) : ℂ)) := by
    funext i
    rw [one_apply_eq_self]
  have hreal : ∀ i, (((inner ℂ (d i) (A (d i)) : ℂ)).re : ℂ) = (inner ℂ (d i) (A (d i)) : ℂ) :=
    fun i => by
      have hconj : starRingEnd ℂ (inner ℂ (d i) (A (d i)) : ℂ) = (inner ℂ (d i) (A (d i)) : ℂ) := by
        rw [inner_conj_symm]
        exact hAsym (d i) (d i)
      exact Complex.conj_eq_iff_re.mp hconj
  have hcast :=
    (hasSum_inner_apply_eq_spectralTrace hAcpt hAsym hAsum d).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  simp_rw [hreal] at hcast
  unfold innerHS
  rw [hone]
  exact hcast.tsum_eq

end ContinuousLinearMap

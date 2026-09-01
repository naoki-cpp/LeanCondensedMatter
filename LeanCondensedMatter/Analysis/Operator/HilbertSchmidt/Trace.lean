import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops

/-!
# Reconciling `innerHS` with `spectralTrace`

For a compact self-adjoint spectrally summable operator, the Hilbert–Schmidt inner product against
the identity agrees with its spectral trace. Diagonal matrix elements are transported through
`selfAdjoint ℂ`; no real-part projection is used.
-/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a compact self-adjoint spectrally summable `A`, `innerHS d 1 A` agrees with the spectral
trace of `A`. -/
theorem innerHS_one_eq_spectralTrace {A : H →L[ℂ] H} (hAcpt : IsCompactOperator A)
    (hAsym : A.IsSymmetric) (hAsum : HasSummableRealEigenvalues A)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    innerHS d 1 A = (spectralTrace A : ℂ) := by
  let hAself : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hAsym
  have hcast :=
    (hasSum_diagonalExpectationValue_eq_spectralTrace hAcpt hAself hAsum d).mapL
      Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  unfold innerHS
  simpa only [one_apply_eq_self] using
    (HasSum.congr_fun hcast fun i =>
      coe_diagonalExpectationValue_right A hAself (d i)).tsum_eq

end ContinuousLinearMap

import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops

set_option linter.style.header false

/-!
# Bundled compact symmetric spectral trace-class hypotheses

`HasSummableRealEigenvalues` deliberately records only spectral summability. The operator theorems
built on the compact spectral theorem additionally require compactness and symmetry, which otherwise
appear repeatedly as three separate proof arguments.

`SpectralTraceClass T` bundles exactly those three hypotheses. The existing unbundled declarations
remain the compatibility API; this module provides shorter theorem forms without changing any
existing statement.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- A compact symmetric operator whose indexed nonzero real eigenvalues are absolutely summable.

This is the precise bundled hypothesis used by the project's spectral trace construction. It is not
a definition of the general trace-class operator ideal. -/
structure SpectralTraceClass (T : H →L[ℂ] H) : Prop where
  compact : IsCompactOperator T
  symmetric : T.IsSymmetric
  summable : HasSummableRealEigenvalues T

namespace SpectralTraceClass

variable {T T' : H →L[ℂ] H}

/-- Build bundled spectral trace-class data for a positive compact operator with summable real
eigenvalues. Positivity supplies symmetry. -/
def ofPositive (hcompact : IsCompactOperator T) (hpos : T.IsPositive)
    (hsummable : HasSummableRealEigenvalues T) : SpectralTraceClass T where
  compact := hcompact
  symmetric := hpos.isSelfAdjoint.isSymmetric
  summable := hsummable

/-- The spectral trace associated with bundled compactness, symmetry, and summability hypotheses. -/
noncomputable def trace (h : SpectralTraceClass T) : ℝ :=
  spectralTrace h.summable

omit [CompleteSpace H] in
/-- The spectral trace of a positive bundled operator is nonnegative. -/
theorem trace_nonneg (h : SpectralTraceClass T)
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) :
    0 ≤ h.trace := by
  simpa [trace] using ContinuousLinearMap.trace_nonneg h.summable hpos

/-- Compute the bundled spectral trace against any Hilbert basis. -/
theorem hasSum_inner_apply (h : SpectralTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) h.trace := by
  simpa [trace] using
    ContinuousLinearMap.hasSum_inner_apply_eq_trace h.compact h.symmetric h.summable d

/-- Bound the diagonal sum over an orthonormal family by the bundled spectral trace. -/
theorem sum_inner_apply_le_trace (h : SpectralTraceClass T)
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) {ι : Type*} {d : ι → H}
    (hd : Orthonormal ℂ d) :
    Summable (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) ∧
      ∑' i, (inner ℂ (d i) (T (d i)) : ℂ).re ≤ h.trace := by
  simpa [trace] using ContinuousLinearMap.sum_inner_apply_le_trace
    h.compact h.symmetric hpos h.summable hd

/-- Additivity of the bundled spectral trace.

This packages the nine proof arguments of `ContinuousLinearMap.trace_add` into the three bundled
hypotheses for `T`, `T'`, and `T + T'`. -/
theorem trace_add (hT : SpectralTraceClass T) (hT' : SpectralTraceClass T')
    (hadd : SpectralTraceClass (T + T')) :
    hadd.trace = hT.trace + hT'.trace := by
  simpa [trace] using ContinuousLinearMap.trace_add
    hT.compact hT.symmetric hT'.compact hT'.symmetric hadd.compact hadd.symmetric
    hT.summable hT'.summable hadd.summable

/-- Cyclicity of the bundled spectral trace for two products.

This packages the ten proof arguments of `ContinuousLinearMap.trace_comp_comm` into bundled
hypotheses for the two factors and their products in both orders. -/
theorem trace_comp_comm (hT : SpectralTraceClass T) (hT' : SpectralTraceClass T')
    (hTT' : SpectralTraceClass (T * T')) (hT'T : SpectralTraceClass (T' * T)) :
    hTT'.trace = hT'T.trace := by
  simpa [trace] using ContinuousLinearMap.trace_comp_comm
    hT.compact hT.symmetric hT'.compact hT'.symmetric
    hTT'.compact hTT'.symmetric hT'T.compact hT'T.symmetric
    hTT'.summable hT'T.summable

end SpectralTraceClass
end ContinuousLinearMap

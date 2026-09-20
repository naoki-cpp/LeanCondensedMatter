import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC

set_option linter.style.header false

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Bundled compact symmetric spectral-trace hypotheses

`SpectralTraceClass T` bundles compactness, symmetry, and absolute summability of the indexed
nonzero real eigenvalues. Bundled declarations are the public operator API; the unbundled theorems
in `Basic` and `Ops` are implementation infrastructure.

The diagonal-expectation API transports self-adjoint matrix elements to `ℝ` only after proving that
they are real. Both the public API and its trace-series implementation use this lossless path.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- A compact symmetric operator whose indexed nonzero real eigenvalues are absolutely summable. -/
structure SpectralTraceClass (T : H →L[ℂ] H) : Prop where
  compact : IsCompactOperator T
  symmetric : T.IsSymmetric
  summable : HasSummableRealEigenvalues T

namespace SpectralTraceClass

variable {T T' : H →L[ℂ] H}

/-- Build bundled spectral-trace data for a positive compact operator with summable real
eigenvalues. Positivity supplies symmetry. -/
theorem ofPositive (hcompact : IsCompactOperator T) (hpos : T.IsPositive)
    (hsummable : HasSummableRealEigenvalues T) : SpectralTraceClass T where
  compact := hcompact
  symmetric := hpos.isSelfAdjoint.isSymmetric
  summable := hsummable

/-- Build bundled spectral-trace data for a continuous functional calculus transform.
Compactness follows from compactness of the original self-adjoint operator together with `f 0 = 0`;
self-adjointness of the transform supplies symmetry. Summability of the transformed nonzero
eigenvalues remains an explicit hypothesis. -/
theorem ofCFC {f : ℝ → ℝ} (hself : IsSelfAdjoint T) (hcompact : IsCompactOperator T)
    (hf : Continuous f) (hf0 : f 0 = 0)
    (hsummable : HasSummableRealEigenvalues (cfc f T)) :
    SpectralTraceClass (cfc f T) where
  compact := isCompactOperator_cfc_of_zero hself hcompact hf hf0
  symmetric := (IsSelfAdjoint.cfc (f := f) (a := T)).isSymmetric
  summable := hsummable

/-- A bundled spectral-trace-class operator is self-adjoint. -/
theorem isSelfAdjoint (h : SpectralTraceClass T) : IsSelfAdjoint T :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr h.symmetric

/-- The spectral trace associated with the bundled hypotheses. -/
noncomputable def trace (h : SpectralTraceClass T) : ℝ :=
  match h with
  | ⟨_, _, _⟩ => ContinuousLinearMap.spectralTrace T

omit [CompleteSpace H] in
@[simp]
theorem trace_eq_spectralTrace (h : SpectralTraceClass T) :
    h.trace = ContinuousLinearMap.spectralTrace T := by
  cases h
  rfl

omit [CompleteSpace H] in
/-- The spectral trace of a positive bundled operator is nonnegative. -/
theorem trace_nonneg (h : SpectralTraceClass T)
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) :
    0 ≤ h.trace := by
  rw [h.trace_eq_spectralTrace]
  exact ContinuousLinearMap.trace_nonneg hpos

/-- A nonzero positive spectral-trace-class operator has strictly positive trace. -/
theorem trace_pos (h : SpectralTraceClass T) (hpos : T.IsPositive) (hne : T ≠ 0) :
    0 < h.trace := by
  classical
  have hnonempty : Nonempty (EigenvectorIndex T) := by
    by_contra hidx
    haveI : IsEmpty (EigenvectorIndex T) := ⟨fun a => hidx ⟨a⟩⟩
    apply hne
    ext x
    have hsum := hasSum_eigenvectorFamily h.compact h.symmetric x
    simpa using hsum.tsum_eq.symm
  let a : EigenvectorIndex T := Classical.choice hnonempty
  have ha_nonneg : 0 ≤ a.1.1 :=
    eigenvalue_nonneg_of_isPositive hpos.toLinearMap a
  have ha_pos : 0 < a.1.1 :=
    lt_of_le_of_ne ha_nonneg (Ne.symm a.1.2)
  have hsum : Summable (fun b : EigenvectorIndex T => b.1.1) :=
    summable_eigenvectorIndex h.summable
  have hle : a.1.1 ≤ spectralTrace T :=
    hsum.le_tsum a (fun b _ => eigenvalue_nonneg_of_isPositive hpos.toLinearMap b)
  rw [← h.trace_eq_spectralTrace] at hle
  exact lt_of_lt_of_le ha_pos hle

/-- Compute the bundled spectral trace against any Hilbert basis using lossless diagonal
expectation values. -/
theorem hasSum_diagonalExpectationValue (h : SpectralTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T h.isSelfAdjoint (d i)) h.trace := by
  rw [h.trace_eq_spectralTrace]
  exact ContinuousLinearMap.hasSum_diagonalExpectationValue_eq_spectralTrace
      h.compact h.isSelfAdjoint h.summable d

/-- Bound the lossless diagonal-expectation sum over an orthonormal family by the bundled spectral
trace. -/
theorem sum_diagonalExpectationValue_le_trace (h : SpectralTraceClass T)
    (hpos : T.IsPositive) {ι : Type*} {d : ι → H}
    (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue T h.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue T h.isSelfAdjoint (d i) ≤ h.trace := by
  rw [h.trace_eq_spectralTrace]
  exact ContinuousLinearMap.sum_diagonalExpectationValue_le_spectralTrace
      h.compact hpos h.summable hd

/-- Additivity of the bundled spectral trace. -/
theorem trace_add (hT : SpectralTraceClass T) (hT' : SpectralTraceClass T')
    (hadd : SpectralTraceClass (T + T')) :
    hadd.trace = hT.trace + hT'.trace := by
  rw [hadd.trace_eq_spectralTrace, hT.trace_eq_spectralTrace, hT'.trace_eq_spectralTrace]
  exact ContinuousLinearMap.spectralTrace_add
    hT.compact hT.symmetric hT'.compact hT'.symmetric hadd.compact hadd.symmetric
    hT.summable hT'.summable hadd.summable

/-- Cyclicity of the bundled spectral trace for two products. The individual factors only need to
be symmetric; compactness and summability are required for the two products whose traces appear. -/
theorem trace_comp_comm (hTsym : T.IsSymmetric) (hT'sym : T'.IsSymmetric)
    (hTT' : SpectralTraceClass (T * T')) (hT'T : SpectralTraceClass (T' * T)) :
    hTT'.trace = hT'T.trace := by
  rw [hTT'.trace_eq_spectralTrace, hT'T.trace_eq_spectralTrace]
  exact ContinuousLinearMap.spectralTrace_comp_comm
    hTsym hT'sym hTT'.compact hTT'.symmetric hT'T.compact hT'T.symmetric
    hTT'.summable hT'T.summable

end SpectralTraceClass
end ContinuousLinearMap

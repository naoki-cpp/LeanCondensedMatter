import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Ops
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC

set_option linter.style.header false

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Bundled compact symmetric spectral trace class

`SpectralTraceClass T` bundles compactness, symmetry, and absolute summability of the indexed
nonzero real eigenvalues. This module is the public spectral operator API and also owns the
compact self-adjoint bridge to general `IsTraceClass` membership and trace norm. The lower-level
spectral theorems in `Basic` and `Ops` remain implementation infrastructure.

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

variable {T : H →L[ℂ] H}

private theorem cfcAbs_apply_eigenvector
    (hself : IsSelfAdjoint T) {v : H} {c : ℝ}
    (hv : (T : H →ₗ[ℂ] H) v = (c : ℂ) • v) :
    CFC.abs T v = ((|c| : ℝ) : ℂ) • v := by
  rw [CFC.abs_eq_cfc_norm T hself]
  simpa only [Real.norm_eq_abs] using
    (cfc_apply_eigenvector (T := T) hself hv (f := fun x : ℝ => ‖x‖) continuous_norm)

/-- Extend the canonical nonzero-eigenvector family of a compact self-adjoint operator to a
Hilbert basis on which the diagonal of `|T|` is `|λ|` on spectral vectors and zero on the
additional basis vectors lying in the kernel. -/
private theorem exists_abs_diagonal_hilbertBasis
    (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    ∃ (u : Set H) (b : HilbertBasis u ℂ H) (j : EigenvectorIndex T → u),
      Function.Injective j ∧
      (∀ a, diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint
        (b (j a)) = |a.1.1|) ∧
      (∀ x, x ∉ Set.range j →
        diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (b x) = 0) := by
  classical
  let hsym : T.IsSymmetric := hself.isSymmetric
  let e : EigenvectorIndex T → H := eigenvectorFamily hcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hcompact hsym
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : EigenvectorIndex T → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  have hb_j (a : EigenvectorIndex T) : b (j a) = e a := by
    rw [hb]
  refine ⟨u, b, j, hj, ?_, ?_⟩
  · intro a
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hb_j,
      cfcAbs_apply_eigenvector hself (apply_eigenvectorFamily hcompact a),
      inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, he.1 a]
    simp
  · intro x hx
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hcompact hsym b j (fun a => by simpa [e] using hb_j a) x hx
    have habs_zero : CFC.abs T (b x) = 0 := by
      simpa using
        cfcAbs_apply_eigenvector hself (v := b x) (c := 0) (by simpa using hxker)
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, habs_zero]
    simp

/-- On compact self-adjoint operators, general trace-class membership is exactly absolute
summability of the nonzero real eigenvalues with multiplicity. -/
theorem isTraceClass_iff_hasSummableRealEigenvalues
    (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    IsTraceClass T ↔ HasSummableRealEigenvalues T := by
  classical
  obtain ⟨u, b, j, hj, hpoint, hzero⟩ :=
    exists_abs_diagonal_hilbertBasis (T := T) hcompact hself
  let g : u → ℝ := fun i =>
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (b i)
  have hg_point (a : EigenvectorIndex T) : g (j a) = |a.1.1| := by
    simpa [g] using hpoint a
  have hg_zero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    simpa [g] using hzero x hx
  constructor
  · intro htrace
    have hg : Summable g := by
      have hbtrace := htrace.isTraceClassWrt b
      simpa [IsTraceClassWrt, g] using hbtrace
    rw [HasSummableRealEigenvalues]
    have hrestricted : Summable (g ∘ j) := hg.comp_injective hj
    exact hrestricted.congr fun a => hg_point a
  · intro hspec
    have hweights : Summable (fun a : EigenvectorIndex T => |a.1.1|) := hspec
    have hrestricted :
        HasSum (g ∘ j) (∑' a : EigenvectorIndex T, |a.1.1|) := by
      change HasSum (fun a => g (j a)) _
      exact HasSum.congr_fun hweights.hasSum hg_point
    have hfull : HasSum g (∑' a : EigenvectorIndex T, |a.1.1|) :=
      (hj.hasSum_iff hg_zero).mp hrestricted
    apply IsTraceClass.of_isTraceClassWrt (d := b)
    simpa [IsTraceClassWrt, g] using hfull.summable

/-- On compact self-adjoint operators, the general complex trace agrees with the real spectral
trace after coercion to `ℂ`. -/
theorem IsTraceClass.trace_eq_spectralTrace
    (hT : IsTraceClass T) (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    hT.trace = (spectralTrace T : ℂ) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [hT.trace_eq_seriesWrt d]
  unfold traceSeriesWrt
  have hspec : HasSummableRealEigenvalues T :=
    (isTraceClass_iff_hasSummableRealEigenvalues hcompact hself).1 hT
  have hcast :=
    (hasSum_diagonalExpectationValue_eq_spectralTrace hcompact hself hspec d).mapL
      Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  exact
    (HasSum.congr_fun hcast fun i =>
      (coe_diagonalExpectationValue_right T hself (d i)).symm).tsum_eq

/-- On compact self-adjoint operators, the canonical trace norm is the absolute eigenvalue sum
with multiplicity. -/
theorem IsTraceClass.traceNorm_eq_tsum_abs_eigenvalues
    (hT : IsTraceClass T) (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    hT.traceNorm = ∑' a : EigenvectorIndex T, |a.1.1| := by
  classical
  obtain ⟨u, b, j, hj, hpoint, hzero⟩ :=
    exists_abs_diagonal_hilbertBasis (T := T) hcompact hself
  let g : u → ℝ := fun i =>
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (b i)
  have hg_point (a : EigenvectorIndex T) : g (j a) = |a.1.1| := by
    simpa [g] using hpoint a
  have hg_zero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    simpa [g] using hzero x hx
  have hg : Summable g := by
    have hbtrace := hT.isTraceClassWrt b
    simpa [IsTraceClassWrt, g] using hbtrace
  have htrace : hT.traceNorm = ∑' i, g i := by
    simpa [g] using hT.traceNorm_eq_tsum_diagonalExpectationValue b
  have hrestricted : HasSum (g ∘ j) (∑' i, g i) :=
    (hj.hasSum_iff hg_zero).mpr hg.hasSum
  have habs : HasSum (fun a : EigenvectorIndex T => |a.1.1|) (∑' i, g i) :=
    HasSum.congr_fun hrestricted fun a => (hg_point a).symm
  exact htrace.trans habs.tsum_eq.symm

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

/-- Bundled compact self-adjoint spectral trace-class data supplies general trace-class
membership. -/
theorem isTraceClass (h : SpectralTraceClass T) : IsTraceClass T :=
  (isTraceClass_iff_hasSummableRealEigenvalues h.compact h.isSelfAdjoint).2 h.summable

/-- The general trace norm of bundled spectral trace-class data is the absolute eigenvalue sum. -/
theorem traceNorm_eq_tsum_abs_eigenvalues (h : SpectralTraceClass T) :
    h.isTraceClass.traceNorm = ∑' a : EigenvectorIndex T, |a.1.1| :=
  h.isTraceClass.traceNorm_eq_tsum_abs_eigenvalues h.compact h.isSelfAdjoint

/-- The spectral trace associated with the bundled hypotheses. -/
noncomputable def trace (_h : SpectralTraceClass T) : ℝ :=
  ContinuousLinearMap.spectralTrace T

omit [CompleteSpace H] in
@[simp]
theorem trace_eq_spectralTrace (h : SpectralTraceClass T) :
    h.trace = ContinuousLinearMap.spectralTrace T :=
  rfl

/-- The general complex trace of bundled spectral trace-class data agrees with its real spectral
trace after coercion to `ℂ`. -/
theorem generalTrace_eq_trace (h : SpectralTraceClass T) :
    h.isTraceClass.trace = (h.trace : ℂ) := by
  rw [h.isTraceClass.trace_eq_spectralTrace h.compact h.isSelfAdjoint,
    h.trace_eq_spectralTrace]

/-- For a positive bundled spectral trace-class operator, the general trace norm agrees with the
spectral trace. -/
theorem traceNorm_eq_trace (h : SpectralTraceClass T) (hpos : T.IsPositive) :
    h.isTraceClass.traceNorm = h.trace := by
  rw [h.traceNorm_eq_tsum_abs_eigenvalues, h.trace_eq_spectralTrace]
  unfold spectralTrace
  apply tsum_congr
  intro a
  exact abs_of_nonneg (eigenvalue_nonneg_of_isPositive hpos.toLinearMap a)

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
  have hbound := h.isTraceClass.sum_diagonalExpectationValue_le_traceNorm hpos hd
  rw [h.traceNorm_eq_trace hpos] at hbound
  simpa using hbound

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

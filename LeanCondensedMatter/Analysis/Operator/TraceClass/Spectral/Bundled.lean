import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.TraceClass.Compact
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Ops
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC

set_option linter.style.header false

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Bundled self-adjoint spectral trace class

`SpectralTraceClass T` bundles general trace-class membership and symmetry. Compactness follows
from general trace-class compactness, while absolute summability of the indexed nonzero real
eigenvalues follows from the compact self-adjoint spectral characterization. This module is the
public spectral operator API and owns the bridge between the general and spectral presentations.
The lower-level spectral theorems in `Basic` and `Ops` remain implementation infrastructure.

The diagonal-expectation API transports self-adjoint matrix elements to `ℝ` only after proving that
they are real. Both the public API and its trace-series implementation use this lossless path.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- A symmetric trace-class operator, with compactness and spectral summability derived. -/
structure SpectralTraceClass (T : H →L[ℂ] H) : Prop where
  isTraceClass : IsTraceClass T
  symmetric : T.IsSymmetric

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
      have hbtrace := (isTraceClass_iff_isTraceClassWrt b T).mp htrace
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
    apply (isTraceClass_iff_isTraceClassWrt b T).mpr
    simpa [IsTraceClassWrt, g] using hfull.summable

/-- A self-adjoint trace-class operator has absolutely summable nonzero real eigenvalues. -/
theorem IsTraceClass.hasSummableRealEigenvalues
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    HasSummableRealEigenvalues T :=
  (isTraceClass_iff_hasSummableRealEigenvalues hT.isCompact hself).1 hT

/-- On self-adjoint trace-class operators, the general complex trace agrees with the real spectral
trace after coercion to `ℂ`. -/
theorem IsTraceClass.trace_eq_spectralTrace
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    hT.trace = (spectralTrace T : ℂ) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [hT.trace_eq_seriesWrt d]
  unfold traceSeriesWrt
  have hspec : HasSummableRealEigenvalues T := hT.hasSummableRealEigenvalues hself
  have hcast :=
    (hasSum_diagonalExpectationValue_eq_spectralTrace hT.isCompact hself hspec d).mapL
      Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  exact
    (HasSum.congr_fun hcast fun i =>
      (coe_diagonalExpectationValue_right T hself (d i)).symm).tsum_eq

/-- On self-adjoint trace-class operators, the canonical trace norm is the absolute eigenvalue sum
with multiplicity. -/
theorem IsTraceClass.traceNorm_eq_tsum_abs_eigenvalues
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    hT.traceNorm = ∑' a : EigenvectorIndex T, |a.1.1| := by
  classical
  obtain ⟨u, b, j, hj, hpoint, hzero⟩ :=
    exists_abs_diagonal_hilbertBasis (T := T) hT.isCompact hself
  let g : u → ℝ := fun i =>
    diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (b i)
  have hg_point (a : EigenvectorIndex T) : g (j a) = |a.1.1| := by
    simpa [g] using hpoint a
  have hg_zero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    simpa [g] using hzero x hx
  have hg : Summable g := by
    have hbtrace := (isTraceClass_iff_isTraceClassWrt b T).mp hT
    simpa [IsTraceClassWrt, g] using hbtrace
  have htrace : hT.traceNorm = ∑' i, g i := by
    simpa [g] using hT.traceNorm_eq_tsum_diagonalExpectationValue b
  have hrestricted : HasSum (g ∘ j) (∑' i, g i) :=
    (hj.hasSum_iff hg_zero).mpr hg.hasSum
  have habs : HasSum (fun a : EigenvectorIndex T => |a.1.1|) (∑' i, g i) :=
    HasSum.congr_fun hrestricted fun a => (hg_point a).symm
  exact htrace.trans habs.tsum_eq.symm

namespace SpectralTraceClass

variable {T : H →L[ℂ] H}

/-- A bundled spectral-trace-class operator is self-adjoint. -/
theorem isSelfAdjoint (h : SpectralTraceClass T) : IsSelfAdjoint T :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr h.symmetric

/-- Every bundled spectral-trace-class operator is compact, by general trace-class compactness. -/
theorem compact (h : SpectralTraceClass T) : IsCompactOperator T :=
  h.isTraceClass.isCompact

/-- Every bundled spectral-trace-class operator has absolutely summable nonzero real eigenvalues. -/
theorem summable (h : SpectralTraceClass T) : HasSummableRealEigenvalues T :=
  h.isTraceClass.hasSummableRealEigenvalues h.isSelfAdjoint

/-- Build bundled spectral-trace data for a positive compact operator with summable real
eigenvalues. Positivity supplies symmetry; spectral summability supplies general trace class. -/
theorem ofPositive (hcompact : IsCompactOperator T) (hpos : T.IsPositive)
    (hsummable : HasSummableRealEigenvalues T) : SpectralTraceClass T where
  isTraceClass :=
    (isTraceClass_iff_hasSummableRealEigenvalues hcompact hpos.isSelfAdjoint).2 hsummable
  symmetric := hpos.isSelfAdjoint.isSymmetric

/-- Build bundled spectral-trace data for a continuous functional calculus transform.
Compactness follows from compactness of the original self-adjoint operator together with `f 0 = 0`;
self-adjointness of the transform supplies symmetry. Summability of the transformed nonzero
eigenvalues supplies general trace class. -/
theorem ofCFC {f : ℝ → ℝ} (hself : IsSelfAdjoint T) (hcompact : IsCompactOperator T)
    (hf : Continuous f) (hf0 : f 0 = 0)
    (hsummable : HasSummableRealEigenvalues (cfc f T)) :
    SpectralTraceClass (cfc f T) := by
  let hcompact' : IsCompactOperator (cfc f T) :=
    isCompactOperator_cfc_of_zero hself hcompact hf hf0
  let hself' : IsSelfAdjoint (cfc f T) := IsSelfAdjoint.cfc (f := f) (a := T)
  exact
    { isTraceClass :=
        (isTraceClass_iff_hasSummableRealEigenvalues hcompact' hself').2 hsummable
      symmetric := hself'.isSymmetric }

/-- For a positive bundled spectral trace-class operator, the general trace norm agrees with the
real spectral trace. -/
theorem traceNorm_eq_spectralTrace (h : SpectralTraceClass T) (hpos : T.IsPositive) :
    h.isTraceClass.traceNorm = spectralTrace T := by
  rw [h.isTraceClass.traceNorm_eq_tsum_abs_eigenvalues h.isSelfAdjoint]
  unfold spectralTrace
  apply tsum_congr
  intro a
  exact abs_of_nonneg (eigenvalue_nonneg_of_isPositive hpos.toLinearMap a)

/-- A nonzero positive spectral-trace-class operator has strictly positive real spectral trace. -/
theorem spectralTrace_pos (h : SpectralTraceClass T) (hpos : T.IsPositive) (hne : T ≠ 0) :
    0 < spectralTrace T := by
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
  exact lt_of_lt_of_le ha_pos hle

/-- Compute the real spectral trace against any Hilbert basis using lossless diagonal expectation
values. -/
theorem hasSum_diagonalExpectationValue (h : SpectralTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T h.isSelfAdjoint (d i)) (spectralTrace T) :=
  ContinuousLinearMap.hasSum_diagonalExpectationValue_eq_spectralTrace
    h.compact h.isSelfAdjoint h.summable d

/-- Bound the lossless diagonal-expectation sum over an orthonormal family by the real spectral
trace. -/
theorem sum_diagonalExpectationValue_le_spectralTrace (h : SpectralTraceClass T)
    (hpos : T.IsPositive) {ι : Type*} {d : ι → H}
    (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue T h.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue T h.isSelfAdjoint (d i) ≤ spectralTrace T := by
  have hbound := h.isTraceClass.sum_diagonalExpectationValue_le_traceNorm hpos hd
  rw [h.traceNorm_eq_spectralTrace hpos] at hbound
  simpa using hbound

end SpectralTraceClass
end ContinuousLinearMap

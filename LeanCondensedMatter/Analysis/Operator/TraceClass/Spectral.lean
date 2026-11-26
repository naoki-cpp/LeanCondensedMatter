import LeanCondensedMatter.Analysis.Operator.HilbertBasis
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real
import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation

set_option linter.style.header false

/-!
# Spectral trace class and trace formulas

The spectral summability predicate and spectral trace use the indexed nonzero real eigenvalues
with multiplicity. Compactness and self-adjointness are explicit hypotheses for spectral expansion.
For compact self-adjoint operators, absolute spectral summability is equivalent to general
trace-class membership, and the eigenvalue sums recover the complex trace and trace norm.
`SpectralTraceClass T` bundles general trace-class membership and symmetry; compactness and
summability are derived. Diagonal expectations are transported losslessly to real scalars.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The absolute values of the indexed nonzero real eigenvalues of `T`, with multiplicity, are
summable.

For the compact self-adjoint operators used by this project, this is the spectral summability
condition underlying spectral-trace arguments. The predicate itself deliberately does **not** assert
compactness or symmetry; those hypotheses are supplied separately wherever the spectral theorem is
used.

No separate "independent of the choice of eigenbasis" lemma is needed here: `EigenvectorIndex T`
and the eigenvalue recorded at each index (`a.1.1`) depend only on the eigenspaces of `T` and their
dimensions, not on which orthonormal basis `stdOrthonormalBasis` happens to pick within each
(possibly multi-dimensional) eigenspace. -/
def HasSummableRealEigenvalues (T : H →L[ℂ] H) : Prop :=
  Summable (fun a : EigenvectorIndex T => |a.1.1|)

/-- The (totalized) spectral sum of the indexed nonzero real eigenvalues of `T`, with
multiplicity.  As for Mathlib's `tsum`, this definition is available for every operator; theorems
that identify or manipulate the sum state `HasSummableRealEigenvalues T` explicitly. -/
noncomputable def spectralTrace (T : H →L[ℂ] H) : ℝ :=
  ∑' a : EigenvectorIndex T, a.1.1

omit [CompleteSpace H] in
/-- Splits the spectral-trace `tsum` over `EigenvectorIndex S` into an outer sum over the
base nonzero eigenvalues and an inner finite sum over each eigenspace's basis vectors. -/
theorem tsum_eigenvectorIndex_eq_tsum_mul_finrank {S : H →L[ℂ] H}
    (hS : Summable (fun a : EigenvectorIndex S => a.1.1)) :
    ∑' a : EigenvectorIndex S, a.1.1 =
      ∑' μ : { ν : ℝ // ν ≠ 0 },
        (Module.finrank ℂ (Module.End.eigenspace (S : H →ₗ[ℂ] H) (μ.1 : ℂ)) : ℝ) * μ.1 := by
  have hsplit : ∑' a : EigenvectorIndex S, a.1.1 =
      ∑' (μ : { ν : ℝ // ν ≠ 0 }) (i : Fin (Module.finrank ℂ
        (Module.End.eigenspace (S : H →ₗ[ℂ] H) (μ.1 : ℂ)))), (⟨μ, i⟩ : EigenvectorIndex S).1.1 :=
    hS.tsum_sigma
  rw [hsplit]
  refine tsum_congr fun μ => ?_
  simp [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The eigenvector expansion of a compact self-adjoint operator, paired with a vector, sums to the
lossless real diagonal expectation. -/
theorem hasSum_eigen_expansion_diagonalExpectationValue
    (hT : IsCompactOperator T) (hTself : IsSelfAdjoint T) (x : H) :
    HasSum (fun a : EigenvectorIndex T =>
      a.1.1 * ‖(inner ℂ (eigenvectorFamily hT a) x : ℂ)‖ ^ 2)
      (diagonalExpectationValue T hTself x) := by
  set e := eigenvectorFamily hT with he_def
  have hs := (hasSum_eigenvectorFamily hT hTself.isSymmetric x).mapL (innerSL ℂ x)
  rw [← he_def] at hs
  have hs' :
      HasSum (fun a : EigenvectorIndex T =>
        ((a.1.1 * ‖(inner ℂ (e a) x : ℂ)‖ ^ 2 : ℝ) : ℂ))
        (inner ℂ x (T x)) := by
    simpa using HasSum.congr_fun hs fun a => by
      symm
      have hstep : (innerSL ℂ x ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a) : ℂ)
          = (a.1.1 : ℂ) * (inner ℂ (e a) x * inner ℂ x (e a) : ℂ) := by
        simp
      rw [hstep, show (inner ℂ x (e a) : ℂ) =
          starRingEnd ℂ (inner ℂ (e a) x) from (inner_conj_symm x (e a)).symm,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [← coe_diagonalExpectationValue_right T hTself x] at hs'
  exact Complex.hasSum_ofReal.mp hs'

end ContinuousLinearMap

/-! ## General trace-class and spectral presentations -/

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

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

/-- A diagonal transform of a compact self-adjoint operator has a basis whose diagonal
series agrees with the corresponding transformed nonzero eigenvalue series. The transform must
vanish on the kernel; the sum equivalence does not require summability in advance. -/
private theorem exists_diagonal_hilbertBasis_hasSum_iff
    (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T)
    {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (happly : ∀ (v : H) (c : ℝ),
      (T : H →ₗ[ℂ] H) v = (c : ℂ) • v → S v = (f c : ℂ) • v) :
    ∃ (u : Set H) (b : HilbertBasis u ℂ H), ∀ c : ℝ,
      HasSum (fun i => diagonalExpectationValue S hS (b i)) c ↔
      HasSum (fun a : EigenvectorIndex T => f a.1.1) c := by
  classical
  let hsym : T.IsSymmetric := hself.isSymmetric
  let e : EigenvectorIndex T → H := eigenvectorFamily hcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hcompact hsym
  obtain ⟨u, b, j, hj, hb_j⟩ := he.exists_hilbertBasis_extension_injective
  let g : u → ℝ := fun i => diagonalExpectationValue S hS (b i)
  have hpoint (a : EigenvectorIndex T) : g (j a) = f a.1.1 := by
    change diagonalExpectationValue S hS (b (j a)) = f a.1.1
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hb_j,
      happly (e a) a.1.1 (apply_eigenvectorFamily hcompact a),
      inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, he.1 a]
    simp
  have hzero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    change diagonalExpectationValue S hS (b x) = 0
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hcompact hsym b j (fun a => by simpa [e] using hb_j a) x hx
    have hSzero : S (b x) = 0 := by
      simpa only [hf0, Complex.ofReal_zero, zero_smul] using
        happly (b x) 0 (by simpa using hxker)
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hSzero]
    simp
  refine ⟨u, b, fun c => ?_⟩
  change HasSum g c ↔ HasSum (fun a : EigenvectorIndex T => f a.1.1) c
  constructor
  · intro hfull
    have hrestricted : HasSum (g ∘ j) c := (hj.hasSum_iff hzero).mpr hfull
    exact hrestricted.congr_fun fun a => (hpoint a).symm
  · intro hweights
    have hrestricted : HasSum (g ∘ j) c := HasSum.congr_fun hweights hpoint
    exact (hj.hasSum_iff hzero).mp hrestricted

/-- On compact self-adjoint operators, general trace-class membership is exactly absolute
summability of the nonzero real eigenvalues with multiplicity. -/
theorem isTraceClass_iff_hasSummableRealEigenvalues
    (hcompact : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    IsTraceClass T ↔ HasSummableRealEigenvalues T := by
  obtain ⟨u, b, hb⟩ := exists_diagonal_hilbertBasis_hasSum_iff hcompact hself
    (CFC.abs_nonneg T).isSelfAdjoint abs abs_zero
    (fun _ _ hv => cfcAbs_apply_eigenvector hself hv)
  constructor
  · intro htrace
    exact ((hb _).mp (htrace.hasSum_abs_diagonalExpectationValue b)).summable
  · intro hspec
    have hweights : Summable (fun a : EigenvectorIndex T => |a.1.1|) := hspec
    exact (isTraceClass_iff_isTraceClassWrt b T).mpr ((hb _).mpr hweights.hasSum).summable

/-- A self-adjoint trace-class operator has absolutely summable nonzero real eigenvalues. -/
theorem IsTraceClass.hasSummableRealEigenvalues
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    HasSummableRealEigenvalues T :=
  (isTraceClass_iff_hasSummableRealEigenvalues hT.isCompact hself).1 hT

/-- `spectralTrace` can be computed against any Hilbert basis using lossless diagonal expectation
values. -/
theorem hasSum_diagonalExpectationValue_eq_spectralTrace
    (hT : IsCompactOperator T) (hTself : IsSelfAdjoint T)
    (h : HasSummableRealEigenvalues T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T hTself (d i)) (spectralTrace T) := by
  have htrace : IsTraceClass T :=
    (isTraceClass_iff_hasSummableRealEigenvalues hT hTself).mpr h
  obtain ⟨u, b, hb⟩ := exists_diagonal_hilbertBasis_hasSum_iff hT hTself
    hTself (fun c => c) rfl (fun _ _ hv => hv)
  have heq : htrace.realTrace hTself = spectralTrace T :=
    ((hb _).mp (htrace.hasSum_realTrace hTself b)).tsum_eq.symm
  rw [← heq]
  exact htrace.hasSum_realTrace hTself d

/-- On self-adjoint trace-class operators, the general complex trace agrees with the real spectral
trace after coercion to `ℂ`. -/
theorem IsTraceClass.trace_eq_spectralTrace
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    hT.trace = (spectralTrace T : ℂ) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hcast :=
    (hasSum_diagonalExpectationValue_eq_spectralTrace hT.isCompact hself
      (hT.hasSummableRealEigenvalues hself) d).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  exact (hT.hasSum_trace d).unique
    (hcast.congr_fun fun i => (coe_diagonalExpectationValue_right T hself (d i)).symm)

/-- On self-adjoint trace-class operators, the canonical trace norm is the absolute eigenvalue sum
with multiplicity. -/
theorem IsTraceClass.traceNorm_eq_tsum_abs_eigenvalues
    (hT : IsTraceClass T) (hself : IsSelfAdjoint T) :
    hT.traceNorm = ∑' a : EigenvectorIndex T, |a.1.1| := by
  obtain ⟨u, b, hb⟩ := exists_diagonal_hilbertBasis_hasSum_iff hT.isCompact hself
    (CFC.abs_nonneg T).isSelfAdjoint abs abs_zero
    (fun _ _ hv => cfcAbs_apply_eigenvector hself hv)
  exact ((hb _).mp (hT.hasSum_abs_diagonalExpectationValue b)).tsum_eq.symm

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
  let hcompact' : IsCompactOperator (cfc f T : H →L[ℂ] H) :=
    isCompactOperator_cfc_of_zero hself hcompact hf hf0
  let hself' : IsSelfAdjoint (cfc f T : H →L[ℂ] H) :=
    IsSelfAdjoint.cfc (f := f) (a := T)
  exact
    { isTraceClass :=
        (isTraceClass_iff_hasSummableRealEigenvalues hcompact' hself').2 hsummable
      symmetric := hself'.isSymmetric }

/-- For a positive bundled spectral trace-class operator, the general trace norm agrees with the
real spectral trace. -/
theorem traceNorm_eq_spectralTrace (h : SpectralTraceClass T) (hpos : T.IsPositive) :
    h.isTraceClass.traceNorm = spectralTrace T := by
  calc
    h.isTraceClass.traceNorm =
        h.isTraceClass.realTrace h.isSelfAdjoint :=
      h.isTraceClass.traceNorm_eq_realTrace hpos
    _ = spectralTrace T := by
      apply Complex.ofReal_injective
      rw [h.isTraceClass.coe_realTrace h.isSelfAdjoint,
        h.isTraceClass.trace_eq_spectralTrace h.isSelfAdjoint]

/-- A nonzero positive spectral-trace-class operator has strictly positive real spectral trace. -/
theorem spectralTrace_pos (h : SpectralTraceClass T) (hpos : T.IsPositive) (hne : T ≠ 0) :
    0 < spectralTrace T := by
  rw [← h.traceNorm_eq_spectralTrace hpos, h.isTraceClass.traceNorm_eq_realTrace hpos]
  exact h.isTraceClass.realTrace_pos hpos hne

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

/-! ## Spectral trace for positive diagonal operators -/

noncomputable section

namespace HilbertBasis

open ContinuousLinearMap

variable {ι : Type*}

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
  let T := diagonalOp b (fun i => (a i : ℂ))
  let hstc := diagonalOpSpectralTraceClass b a ha ha_nonneg
  have htrace := hstc.hasSum_diagonalExpectationValue b
  have hpoint :
      (fun i => diagonalExpectationValue T hstc.isSelfAdjoint (b i)) = a := by
    funext i
    simpa [T] using diagonalExpectationValue_diagonalOp b a ha ha_nonneg i
  change HasSum (fun i => diagonalExpectationValue T hstc.isSelfAdjoint (b i))
    (spectralTrace T) at htrace
  rw [hpoint] at htrace
  exact htrace.tsum_eq.symm

end HilbertBasis

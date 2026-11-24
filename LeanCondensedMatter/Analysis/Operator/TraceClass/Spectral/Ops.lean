import LeanCondensedMatter.Analysis.HilbertBasis
import LeanCondensedMatter.Analysis.InfiniteSum.Order
import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation

set_option linter.style.header false

/-!
# Spectral trace definitions, basis formulas, product commutation, and equality

This module also owns spectral summability and `spectralTrace` via the indexed nonzero
eigenvalues of compact self-adjoint operators. The Hilbert-basis formulas compare
compact self-adjoint operators against a common basis rather
than choosing unrelated eigenbases. Diagonal matrix elements are transported through
`selfAdjoint ℂ` before being treated as real scalars.

For self-adjoint factors, a self-adjoint product already implies that the factors commute, so
equality of their product spectral traces does not require spectral summability. This special
case is not the general trace-cyclicity theorem for noncommuting bounded factors.

The positivity-based equality criterion additionally identifies saturation of the spectral
trace with completeness of the orthonormal family.
-/

/-!
# Spectral summability and spectral trace for compact self-adjoint operators

This module defines `HasSummableRealEigenvalues` and `spectralTrace` using the countable
nonzero-eigenvector family of a compact self-adjoint operator.

The resulting notion is intentionally narrower than a general trace-class ideal: it records
absolute summability of the indexed nonzero real eigenvalues. Compactness and self-adjointness
remain explicit hypotheses of the operator theorems that use the spectral expansion.
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
/-- Every eigenvalue of a positive operator is nonnegative. -/
theorem eigenvalue_nonneg_of_isPositive {T : H →L[ℂ] H} (hpos : (T : H →ₗ[ℂ] H).IsPositive)
    (a : EigenvectorIndex T) : 0 ≤ a.1.1 := by
  have hpos_finrank : 0 < Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ)) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) a.2.isLt
  have hne : Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot ℂ H] at hpos_finrank
    exact absurd hpos_finrank (lt_irrefl 0)
  exact eigenvalue_nonneg_of_nonneg hne hpos.re_inner_nonneg_right

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

/-- `spectralTrace` can be computed against any Hilbert basis using lossless diagonal expectation
values. -/
theorem hasSum_diagonalExpectationValue_eq_spectralTrace
    (hT : IsCompactOperator T) (hTself : IsSelfAdjoint T)
    (h : HasSummableRealEigenvalues T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => diagonalExpectationValue T hTself (d i)) (spectralTrace T) := by
  classical
  change HasSum (fun i => diagonalExpectationValue T hTself (d i))
    (∑' a : EigenvectorIndex T, a.1.1)
  set e := eigenvectorFamily hT with he_def
  set f : EigenvectorIndex T → ι → ℝ :=
    fun a i => a.1.1 * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2 with hf_def
  have hparseval : ∀ a : EigenvectorIndex T,
      HasSum (fun i => ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2) (1 : ℝ) := fun a => by
    have hsum := d.hasSum_norm_sq_inner (e a)
    rwa [(orthonormal_eigenvectorFamily hT hTself.isSymmetric).1 a, one_pow] at hsum
  have hpoint : ∀ i, HasSum (f · i) (diagonalExpectationValue T hTself (d i)) :=
    fun i => hasSum_eigen_expansion_diagonalExpectationValue hT hTself (d i)
  have hcond1 : ∀ a : EigenvectorIndex T,
      Summable (fun i => |a.1.1| * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2) :=
    fun a => (hparseval a).summable.mul_left _
  have hcond2 : Summable (fun a : EigenvectorIndex T =>
      ∑' i, |a.1.1| * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2) := by
    have heq2 : ∀ a : EigenvectorIndex T,
        ∑' i, |a.1.1| * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2 = |a.1.1| := fun a => by
      rw [tsum_mul_left, (hparseval a).tsum_eq, mul_one]
    have h' : Summable (fun a : EigenvectorIndex T => |a.1.1|) := h
    simpa only [heq2] using h'
  have habs : Summable (fun p : EigenvectorIndex T × ι =>
      |p.1.1.1| * ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖ ^ 2) :=
    (summable_prod_of_nonneg (fun p => by positivity)).mpr ⟨hcond1, hcond2⟩
  have hg : Summable (Function.uncurry f) :=
    Summable.of_abs <| habs.congr fun p => by
      symm
      rw [Function.uncurry, hf_def]
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖)]
  have hpointA : ∀ a : EigenvectorIndex T, HasSum (f a) a.1.1 := fun a => by
    have hsum := (hparseval a).mul_left (a.1.1 : ℝ)
    rwa [mul_one] at hsum
  have hS_eq : (∑' p, Function.uncurry f p) = ∑' a : EigenvectorIndex T, a.1.1 :=
    (hg.hasSum.prod_fiberwise hpointA).tsum_eq.symm
  have hswap2 : Summable (fun q : ι × EigenvectorIndex T => f q.2 q.1) := hg.prod_symm
  have hHS := hswap2.hasSum.prod_fiberwise hpoint
  have hsymmeq : ∑' q : ι × EigenvectorIndex T, f q.2 q.1 =
      ∑' p, Function.uncurry f p :=
    (Equiv.prodComm ι (EigenvectorIndex T)).tsum_eq (Function.uncurry f)
  rwa [hsymmeq, hS_eq] at hHS

/-- For self-adjoint operators, self-adjointness of the product forces the factors to
commute. Their spectral traces therefore agree without compactness or summability assumptions. -/
theorem spectralTrace_comp_comm {T' : H →L[ℂ] H}
    (hTsym : T.IsSymmetric) (hT'sym : T'.IsSymmetric)
    (hTT'sym : (T * T' : H →L[ℂ] H).IsSymmetric) :
    spectralTrace (T * T') = spectralTrace (T' * T) := by
  have hTself : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTsym
  have hT'self : IsSelfAdjoint T' :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT'sym
  have hTT'self : IsSelfAdjoint (T * T') :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTT'sym
  have hcomm : T * T' = T' * T := by
    calc
      T * T' = ContinuousLinearMap.adjoint (T * T') := hTT'self.adjoint_eq.symm
      _ = T' * T := by
        simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul,
          (ContinuousLinearMap.star_eq_adjoint T').trans hT'self.adjoint_eq,
          (ContinuousLinearMap.star_eq_adjoint T).trans hTself.adjoint_eq]
  exact congrArg spectralTrace hcomm

end ContinuousLinearMap

/-! ## Equality case for spectral trace saturation -/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If a positive operator has strictly positive diagonal value on every unit vector, an
orthonormal family can saturate its spectral trace only when its span has trivial orthogonal
complement. -/
theorem orthogonal_span_eq_bot_of_sum_diagonalExpectationValue_eq_spectralTrace
    {T : H →L[ℂ] H} (hT : IsCompactOperator T) (hTpos : T.IsPositive)
    (h : HasSummableRealEigenvalues T)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d)
    (hdiag_pos : ∀ v : H, ‖v‖ = 1 →
      0 < diagonalExpectationValue T hTpos.isSelfAdjoint v)
    (heq : ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) =
      spectralTrace T) :
    (Submodule.span ℂ (Set.range d))ᗮ = ⊥ := by
  classical
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j =>
    diagonalExpectationValue T hTpos.isSelfAdjoint (b j) with hg_def
  have htr : HasSum g (spectralTrace T) :=
    hasSum_diagonalExpectationValue_eq_spectralTrace hT hTpos.isSelfAdjoint h b
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => by
    simpa [g] using diagonalExpectationValue_nonneg T hTpos (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij =>
    hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) =
      diagonalExpectationValue T hTpos.isSelfAdjoint (d i) := fun i => by
    change diagonalExpectationValue T hTpos.isSelfAdjoint (b (e i)) = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have heqg : ∑' i, g (e i) = spectralTrace T := by
    calc
      ∑' i, g (e i) =
          ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) :=
        tsum_congr hge
      _ = spectralTrace T := heq
  have he_surj : Function.Surjective e := by
    by_contra hsurj
    have hsurj' : ∃ j, ∀ i, e i ≠ j := by
      simpa only [Function.Surjective, not_forall, not_exists] using hsurj
    obtain ⟨j, hj⟩ := hsurj'
    have hjrange : j ∉ Set.range e := by
      rintro ⟨i, hi⟩
      exact hj i hi
    have hgjpos : 0 < g j := by
      simpa [g] using hdiag_pos (b j) (b.orthonormal.1 j)
    have hlt := htr.summable.tsum_comp_injective_lt_of_exists_not_mem
      hgnonneg e he_inj hjrange hgjpos
    have hlt_trace : ∑' i, g (e i) < spectralTrace T := by
      rwa [htr.tsum_eq] at hlt
    exact (ne_of_lt hlt_trace) heqg
  apply le_antisymm
  · intro x hx
    have hinner : ∀ j : w, inner ℂ (b j) x = 0 := by
      intro j
      obtain ⟨i, hi⟩ := he_surj j
      have hbdi : b j = d i := by
        rw [← hi]
        rw [hb_eq]
      rw [hbdi]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self i)) hx
    have hrepr : b.repr x = 0 := by
      ext j
      rw [b.repr_apply_apply]
      exact hinner j
    have hx0 : x = 0 := b.repr.injective (by simpa using hrepr)
    rw [hx0]
    exact Submodule.zero_mem _
  · exact bot_le

end ContinuousLinearMap

import LeanCondensedMatter.Analysis.InnerProductSpace.HilbertBasisParseval
import LeanCondensedMatter.Analysis.Operator.TraceClass.Basic

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Spectral-trace linearity, cyclicity, and bounds

The theorems are proved by comparing operators against a common Hilbert basis rather than relating
individually unrelated eigenbases. See `notes/roadmaps/operator-algebra.md` (Track C).
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem inner_mul_inner_conj_eq_norm_sq (x y : H) :
    (inner ℂ x y * inner ℂ y x : ℂ) = ((‖(inner ℂ x y : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [show (inner ℂ y x : ℂ) = starRingEnd ℂ (inner ℂ x y) from (inner_conj_symm y x).symm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- The diagonal sum of a finite-rank orthogonal projection against any Hilbert basis equals its
rank. -/
theorem tsum_norm_sq_orthogonalProjectionOnto_eq_finrank {ι : Type*} (b : HilbertBasis ι ℂ H)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    ∑' i, ‖V.orthogonalProjectionOnto (b i)‖ ^ 2 = (Module.finrank ℂ V : ℝ) := by
  classical
  let f : Fin (Module.finrank ℂ V) → V := ⇑(stdOrthonormalBasis ℂ V)
  have hpoint : ∀ i, ‖V.orthogonalProjectionOnto (b i)‖ ^ 2 =
      ∑ j, ‖(inner ℂ ((f j : H)) (b i) : ℂ)‖ ^ 2 := by
    intro i
    rw [← (stdOrthonormalBasis ℂ V).sum_sq_norm_inner_right (V.orthogonalProjectionOnto (b i))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum fun j _ => (b.hasSum_norm_sq_inner (f j : H)).summable]
  simp_rw [(b.hasSum_norm_sq_inner (f _ : H)).tsum_eq]
  have hnorm1 : ∀ j : Fin (Module.finrank ℂ V), ‖(f j : H)‖ = 1 :=
    fun j => (stdOrthonormalBasis ℂ V).orthonormal.1 j
  simp [hnorm1]

/-- The eigenvector expansion of `T x`, paired with `x`, sums to `⟪x, T x⟫.re`. -/
theorem hasSum_eigen_expansion_inner_apply (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (x : H) :
    HasSum (fun a : EigenvectorIndex T => a.1.1 * ‖(inner ℂ (eigenvectorFamily hT a) x : ℂ)‖ ^ 2)
      (inner ℂ x (T x) : ℂ).re := by
  set e := eigenvectorFamily hT with he_def
  have hs := ((hasSum_eigenvectorFamily hT hT' x).mapL (innerSL ℂ x)).mapL Complex.reCLM
  have heq : (fun a : EigenvectorIndex T => Complex.reCLM ((innerSL ℂ x)
      ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a))) =
      (fun a => a.1.1 * ‖(inner ℂ (e a) x : ℂ)‖ ^ 2) := by
    funext a
    have hstep : (innerSL ℂ x ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a) : ℂ)
        = (a.1.1 : ℂ) * (inner ℂ (e a) x * inner ℂ x (e a) : ℂ) := by
      simp
    change (innerSL ℂ x ((a.1.1 : ℂ) • (inner ℂ (e a) x : ℂ) • e a) : ℂ).re =
      a.1.1 * ‖(inner ℂ (e a) x : ℂ)‖ ^ 2
    rw [hstep, inner_mul_inner_conj_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  rwa [heq] at hs

/-- `spectralTrace` can be computed against any Hilbert basis of `H`. -/
theorem hasSum_inner_apply_eq_spectralTrace (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    (h : HasSummableRealEigenvalues T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) (spectralTrace h) := by
  classical
  change HasSum (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) (∑' a : EigenvectorIndex T, a.1.1)
  set e := eigenvectorFamily hT with he_def
  set f : EigenvectorIndex T → ι → ℝ :=
    fun a i => a.1.1 * ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2 with hf_def
  have hparseval : ∀ a : EigenvectorIndex T, HasSum (fun i => ‖(inner ℂ (e a) (d i) : ℂ)‖ ^ 2)
      (1 : ℝ) := fun a => by
    have := d.hasSum_norm_sq_inner (e a)
    rwa [(orthonormal_eigenvectorFamily hT hT').1 a, one_pow] at this
  have hpoint : ∀ i, HasSum (f · i) (inner ℂ (d i) (T (d i)) : ℂ).re :=
    fun i => hasSum_eigen_expansion_inner_apply hT hT' (d i)
  have hcond1 : ∀ a : EigenvectorIndex T, Summable (fun i => |a.1.1| * ‖(inner ℂ (e a) (d i) :
      ℂ)‖ ^ 2) := fun a => (hparseval a).summable.mul_left _
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
  have hg : Summable (Function.uncurry f) := by
    have heqabs : (fun p : EigenvectorIndex T × ι => |Function.uncurry f p|) =
        (fun p : EigenvectorIndex T × ι =>
          |p.1.1.1| * ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖ ^ 2) := by
      funext p
      rw [Function.uncurry, hf_def]
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(inner ℂ (e p.1) (d p.2) : ℂ)‖)]
    exact Summable.of_abs (by rw [heqabs]; exact habs)
  have hpointA : ∀ a : EigenvectorIndex T, HasSum (f a) a.1.1 := fun a => by
    have := (hparseval a).mul_left (a.1.1 : ℝ)
    rwa [mul_one] at this
  have hS_eq : (∑' p, Function.uncurry f p) = ∑' a : EigenvectorIndex T, a.1.1 :=
    (hg.hasSum.prod_fiberwise hpointA).tsum_eq.symm
  have hswap2 : Summable (fun q : ι × EigenvectorIndex T => f q.2 q.1) := hg.prod_symm
  have hHS := hswap2.hasSum.prod_fiberwise hpoint
  have hsymmeq : ∑' q : ι × EigenvectorIndex T, f q.2 q.1 = ∑' p, Function.uncurry f p :=
    (Equiv.prodComm ι (EigenvectorIndex T)).tsum_eq (Function.uncurry f)
  rwa [hsymmeq, hS_eq] at hHS

/-- Additivity of `spectralTrace`. -/
theorem spectralTrace_add {T' : H →L[ℂ] H} (hT : IsCompactOperator T) (hTsym : T.IsSymmetric)
    (hT' : IsCompactOperator T') (hT'sym : T'.IsSymmetric)
    (hTT' : IsCompactOperator (T + T')) (hTT'sym : (T + T' : H →L[ℂ] H).IsSymmetric)
    (h : HasSummableRealEigenvalues T) (h' : HasSummableRealEigenvalues T')
    (hsum : HasSummableRealEigenvalues (T + T')) :
    spectralTrace hsum = spectralTrace h + spectralTrace h' := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hs1 := hasSum_inner_apply_eq_spectralTrace hT hTsym h d
  have hs2 := hasSum_inner_apply_eq_spectralTrace hT' hT'sym h' d
  have hs3 := hasSum_inner_apply_eq_spectralTrace hTT' hTT'sym hsum d
  have hadd := hs1.add hs2
  have heq : (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re + (inner ℂ (d i) (T' (d i)) : ℂ).re) =
      (fun i => (inner ℂ (d i) ((T + T') (d i)) : ℂ).re) := by
    funext i
    simp [inner_add_right]
  rw [heq] at hadd
  exact (hadd.unique hs3).symm

/-- Cyclicity of `spectralTrace` for two products satisfying the required hypotheses. -/
theorem spectralTrace_comp_comm {T' : H →L[ℂ] H} (_hT : IsCompactOperator T)
    (hTsym : T.IsSymmetric) (_hT' : IsCompactOperator T') (hT'sym : T'.IsSymmetric)
    (hTT' : IsCompactOperator (T * T')) (hTT'sym : (T * T' : H →L[ℂ] H).IsSymmetric)
    (hT'T : IsCompactOperator (T' * T)) (hT'Tsym : (T' * T : H →L[ℂ] H).IsSymmetric)
    (h1 : HasSummableRealEigenvalues (T * T'))
    (h2 : HasSummableRealEigenvalues (T' * T)) :
    spectralTrace h1 = spectralTrace h2 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  have hs1 := hasSum_inner_apply_eq_spectralTrace hTT' hTT'sym h1 d
  have hs2 := hasSum_inner_apply_eq_spectralTrace hT'T hT'Tsym h2 d
  have heq : (fun i => (inner ℂ (d i) ((T * T') (d i)) : ℂ).re) =
      (fun i => (inner ℂ (d i) ((T' * T) (d i)) : ℂ).re) := by
    funext i
    simp only [mul_apply_eq_comp]
    have h1' : (inner ℂ (d i) (T (T' (d i))) : ℂ) = inner ℂ (T (d i)) (T' (d i)) :=
      (hTsym (d i) (T' (d i))).symm
    have h2' : (inner ℂ (d i) (T' (T (d i))) : ℂ) = inner ℂ (T' (d i)) (T (d i)) :=
      (hT'sym (d i) (T (d i))).symm
    rw [h1', h2']
    have h3 : (inner ℂ (T' (d i)) (T (d i)) : ℂ) =
        starRingEnd ℂ (inner ℂ (T (d i)) (T' (d i))) :=
      (inner_conj_symm (T' (d i)) (T (d i))).symm
    rw [h3, Complex.conj_re]
  rw [heq] at hs1
  exact hs1.unique hs2

/-- The sum of diagonal matrix elements of a positive spectrally summable operator against any
orthonormal family is at most its spectral trace. -/
theorem sum_inner_apply_le_spectralTrace {T : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hTsym : T.IsSymmetric) (hTpos : (T : H →ₗ[ℂ] H).IsPositive)
    (h : HasSummableRealEigenvalues T) {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => (inner ℂ (d i) (T (d i)) : ℂ).re) ∧
      ∑' i, (inner ℂ (d i) (T (d i)) : ℂ).re ≤ spectralTrace h := by
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j => (inner ℂ (b j) (T (b j)) : ℂ).re with hg_def
  have htr : HasSum g (spectralTrace h) := hasSum_inner_apply_eq_spectralTrace hT hTsym h b
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => hTpos.re_inner_nonneg_right (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij => hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) = (inner ℂ (d i) (T (d i)) : ℂ).re := fun i => by
    change (inner ℂ (b (e i)) (T (b (e i))) : ℂ).re = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have hfsum : Summable (fun i => g (e i)) := htr.summable.comp_injective he_inj
  have hle : ∑' i, g (e i) ≤ spectralTrace h :=
    hasSum_le_inj e he_inj (fun j _ => hgnonneg j) (fun _ => le_rfl) hfsum.hasSum htr
  refine ⟨hfsum.congr hge, ?_⟩
  rwa [tsum_congr hge] at hle

end ContinuousLinearMap

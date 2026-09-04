import LeanCondensedMatter.Analysis.InnerProductSpace.HilbertBasisParseval
import LeanCondensedMatter.Analysis.Operator.TraceClass.Basic
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation

set_option linter.style.header false

/-!
# Spectral-trace linearity, cyclicity, and bounds

The theorems are proved by comparing operators against a common Hilbert basis rather than relating
individually unrelated eigenbases. Diagonal matrix elements are transported through
`selfAdjoint ℂ` before they are treated as real numbers. See
`notes/roadmaps/operator-algebra.md`.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem inner_mul_inner_conj_eq_norm_sq (x y : H) :
    (inner ℂ x y * inner ℂ y x : ℂ) = ((‖(inner ℂ x y : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [show (inner ℂ y x : ℂ) = starRingEnd ℂ (inner ℂ x y) from (inner_conj_symm y x).symm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

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
      rw [hstep, inner_mul_inner_conj_eq_norm_sq, Complex.ofReal_pow]
  rw [← coe_diagonalExpectationValue_right T hTself x] at hs'
  exact (hasSum_ofReal ℂ).mp hs'

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

/-- Additivity of `spectralTrace`. -/
theorem spectralTrace_add {T' : H →L[ℂ] H} (hT : IsCompactOperator T) (hTsym : T.IsSymmetric)
    (hT' : IsCompactOperator T') (hT'sym : T'.IsSymmetric)
    (hTT' : IsCompactOperator (T + T')) (hTT'sym : (T + T' : H →L[ℂ] H).IsSymmetric)
    (h : HasSummableRealEigenvalues T) (h' : HasSummableRealEigenvalues T')
    (hsum : HasSummableRealEigenvalues (T + T')) :
    spectralTrace (T + T') = spectralTrace T + spectralTrace T' := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let hTself : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTsym
  let hT'self : IsSelfAdjoint T' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT'sym
  let hsumself : IsSelfAdjoint (T + T') :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTT'sym
  have hs1 := hasSum_diagonalExpectationValue_eq_spectralTrace hT hTself h d
  have hs2 := hasSum_diagonalExpectationValue_eq_spectralTrace hT' hT'self h' d
  have hs3 := hasSum_diagonalExpectationValue_eq_spectralTrace hTT' hsumself hsum d
  have hadd := HasSum.congr_fun (hs1.add hs2) fun i =>
    diagonalExpectationValue_add T T' hTself hT'self (d i)
  exact (hadd.unique hs3).symm

/-- Cyclicity of `spectralTrace` for two products satisfying the required hypotheses. -/
theorem spectralTrace_comp_comm {T' : H →L[ℂ] H}
    (hTsym : T.IsSymmetric) (hT'sym : T'.IsSymmetric)
    (hTT' : IsCompactOperator (T * T')) (hTT'sym : (T * T' : H →L[ℂ] H).IsSymmetric)
    (hT'T : IsCompactOperator (T' * T)) (hT'Tsym : (T' * T : H →L[ℂ] H).IsSymmetric)
    (h1 : HasSummableRealEigenvalues (T * T'))
    (h2 : HasSummableRealEigenvalues (T' * T)) :
    spectralTrace (T * T') = spectralTrace (T' * T) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let hTT'self : IsSelfAdjoint (T * T') :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTT'sym
  let hT'Tself : IsSelfAdjoint (T' * T) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT'Tsym
  have hs1 := hasSum_diagonalExpectationValue_eq_spectralTrace hTT' hTT'self h1 d
  have hs2 := hasSum_diagonalExpectationValue_eq_spectralTrace hT'T hT'Tself h2 d
  have hs1' :
      HasSum (fun i => diagonalExpectationValue (T' * T) hT'Tself (d i))
        (spectralTrace (T * T')) :=
    HasSum.congr_fun hs1 fun i => by
      symm
      apply diagonalExpectationValue_eq_of_inner_eq hTT'self hT'Tself (d i)
      simp only [mul_apply_eq_comp]
      have h1' : (inner ℂ (d i) (T (T' (d i))) : ℂ) =
          inner ℂ (T (d i)) (T' (d i)) :=
        (hTsym (d i) (T' (d i))).symm
      have h2' : (inner ℂ (d i) (T' (T (d i))) : ℂ) =
          inner ℂ (T' (d i)) (T (d i)) :=
        (hT'sym (d i) (T (d i))).symm
      have hzdiag : IsSelfAdjoint (inner ℂ (d i) (T (T' (d i)))) := by
        change IsSelfAdjoint (inner ℂ (d i) ((T * T') (d i)))
        rw [← coe_diagonalExpectationValue_right (T * T') hTT'self (d i)]
        exact Complex.conj_ofReal _
      have hz : IsSelfAdjoint (inner ℂ (T (d i)) (T' (d i))) := by
        rw [← h1']
        exact hzdiag
      have hconj : (inner ℂ (T' (d i)) (T (d i)) : ℂ) =
          starRingEnd ℂ (inner ℂ (T (d i)) (T' (d i))) :=
        (inner_conj_symm (T' (d i)) (T (d i))).symm
      rw [h1', h2', hconj]
      exact hz.symm
  exact hs1'.unique hs2

/-- The sum of lossless diagonal expectation values of a positive spectrally summable operator
against any orthonormal family is at most its spectral trace. -/
theorem sum_diagonalExpectationValue_le_spectralTrace
    {T : H →L[ℂ] H} (hT : IsCompactOperator T) (hTpos : T.IsPositive)
    (h : HasSummableRealEigenvalues T) {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => diagonalExpectationValue T hTpos.isSelfAdjoint (d i)) ∧
      ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) ≤ spectralTrace T := by
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j =>
    diagonalExpectationValue T hTpos.isSelfAdjoint (b j) with hg_def
  have htr : HasSum g (spectralTrace T) :=
    hasSum_diagonalExpectationValue_eq_spectralTrace hT hTpos.isSelfAdjoint h b
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => by
    simpa [g] using diagonalExpectationValue_nonneg T hTpos (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij => hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) = diagonalExpectationValue T hTpos.isSelfAdjoint (d i) := fun i => by
    change diagonalExpectationValue T hTpos.isSelfAdjoint (b (e i)) = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have hfsum : Summable (fun i => g (e i)) := htr.summable.comp_injective he_inj
  have hle : ∑' i, g (e i) ≤ spectralTrace T :=
    hasSum_le_inj e he_inj (fun j _ => hgnonneg j) (fun _ => le_rfl) hfsum.hasSum htr
  refine ⟨hfsum.congr hge, ?_⟩
  rwa [tsum_congr hge] at hle

end ContinuousLinearMap

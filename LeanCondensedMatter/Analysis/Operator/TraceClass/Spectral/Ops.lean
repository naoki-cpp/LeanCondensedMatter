import LeanCondensedMatter.Analysis.HilbertBasis
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Basic
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation

set_option linter.style.header false

/-!
# Spectral-trace basis formulas and product commutation

The Hilbert-basis formulas compare compact self-adjoint operators against a common basis rather
than choosing unrelated eigenbases. Diagonal matrix elements are transported through
`selfAdjoint ℂ` before being treated as real scalars.

For self-adjoint factors, a self-adjoint product already implies that the factors commute, so
equality of their product spectral traces does not require spectral summability. This special
case is not the general trace-cyclicity theorem for noncommuting bounded factors.
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
        rw [show ContinuousLinearMap.adjoint (T * T') = star (T * T') from
          (ContinuousLinearMap.star_eq_adjoint (T * T')).symm,
          star_mul, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.star_eq_adjoint,
          hT'self.adjoint_eq, hTself.adjoint_eq]
  exact congrArg spectralTrace hcomm

end ContinuousLinearMap

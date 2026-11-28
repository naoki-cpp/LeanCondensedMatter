import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Positive
import LeanCondensedMatter.Analysis.Operator.Spectral.FunctionalCalculus
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option linter.style.header false

section

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# The Peierls–Bogoliubov spectral inequality and its equality cases

For a self-adjoint bounded operator `T` on a Hilbert space, a unit vector `e`, and a convex
continuous function `g : ℝ → ℝ`, the diagonal matrix element of `g` applied by continuous
functional calculus is bounded below by `g` of the diagonal matrix element of `T`:

`g ⟪e, T e⟫ ≤ ⟪e, cfc g T e⟫`.

The public inequalities are stated in the complex positive order, so they also establish that the
relevant diagonal matrix elements are real rather than discarding an imaginary part with `.re`.

The proof uses an explicit supporting affine minorant for `g` at the relevant scalar point. The
pointwise affine inequality is lifted to an operator inequality by monotonicity of the continuous
functional calculus and then evaluated on the unit vector by positivity. The supporting-line
condition is therefore an explicit theorem hypothesis. For
`g x = exp (-β x)`, `exp_tangent` supplies that hypothesis, yielding the form used in the
Gibbs–Klein and Helmholtz free-energy arguments.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap ComplexOrder
open scoped ComplexOrder

/-- **The Peierls–Bogoliubov inequality.** For a self-adjoint bounded operator `T`, a unit
vector `e`, and a continuous `g : ℝ → ℝ` admitting a tangent line at the lossless real diagonal
expectation `x₀`, `g x₀` is below the diagonal matrix element of `g(T)` in the complex positive
order. -/
theorem peierls_bogoliubov (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (spectrum ℝ T)) (e : H) (he : ‖e‖ = 1)
    (m x₀ : ℝ) (hx0 : x₀ = diagonalExpectationValue T hT e)
    (htangent : ∀ x : ℝ, m * x + (g x₀ - m * x₀) ≤ g x) :
    (g x₀ : ℂ) ≤ inner ℂ (cfc (R := ℝ) g T e) e := by
  have hle : cfc (R := ℝ) (fun x : ℝ => m * x + (g x₀ - m * x₀)) T ≤ cfc (R := ℝ) g T :=
    cfc_mono (fun x _ => htangent x)
  rw [ContinuousLinearMap.le_def] at hle
  have hpos := hle.inner_nonneg_left e
  rw [cfc_add T (fun x => m * x) (fun x => g x₀ - m * x₀) (by fun_prop) (by fun_prop)] at hpos
  rw [cfc_const (R := ℝ) (g x₀ - m * x₀) T,
    show (fun x : ℝ => m * x) = fun x => m • x from rfl,
    cfc_smul_id (R := ℝ) m T, Algebra.algebraMap_eq_smul_one] at hpos
  have hreal : ∀ (r : ℝ) (x y : H), (inner ℂ (r • x) y : ℂ) = (r : ℂ) * inner ℂ x y := by
    intro r x y
    rw [← algebraMap_smul ℂ r x, RCLike.algebraMap_eq_ofReal, inner_smul_real_left,
      Complex.real_smul]
  simp only [sub_apply, add_apply, smul_apply, one_apply_eq_self, inner_sub_left,
    inner_add_left, hreal] at hpos
  have hnorm : (inner ℂ e e : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  rw [hnorm, mul_one] at hpos
  have hx0c : (x₀ : ℂ) = inner ℂ (T e) e := by
    rw [hx0]
    exact coe_diagonalExpectationValue T hT e
  rw [← hx0c] at hpos
  have hcollapse :
      (m : ℂ) * (x₀ : ℂ) + ((g x₀ - m * x₀ : ℝ) : ℂ) = (g x₀ : ℂ) := by
    push_cast
    ring
  rw [hcollapse] at hpos
  exact sub_nonneg.mp hpos

/-- The tangent-line minorant for `x ↦ exp(-β x)` at `x₀`, discharging `peierls_bogoliubov`'s
`htangent` hypothesis for this concrete `g` (the case needed for the Gibbs state
`e^{-βH}`). Proved directly from `Real.add_one_le_exp`, without any general convexity
machinery. -/
theorem exp_tangent (β x₀ x : ℝ) :
    (-β * Real.exp (-β * x₀)) * x + (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)
      ≤ Real.exp (-β * x) := by
  have h := Real.add_one_le_exp (-β * (x - x₀))
  have hexp : Real.exp (-β * x) = Real.exp (-β * x₀) * Real.exp (-β * (x - x₀)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp]
  nlinarith [Real.exp_pos (-β * x₀), h]

/-- **Peierls–Bogoliubov, specialized to the Gibbs weight `g = exp(-β·)`.** The inequality is
stated directly in the complex positive order, so it also records the reality of the Gibbs
diagonal matrix element. -/
theorem gibbs_peierls_bogoliubov (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (β : ℝ) (e : H)
    (he : ‖e‖ = 1) :
    (Real.exp (-β * diagonalExpectationValue T hT e) : ℂ) ≤
      inner ℂ (cfc (R := ℝ) (fun x => Real.exp (-β * x)) T e) e :=
  peierls_bogoliubov T hT (fun x => Real.exp (-β * x)) (by fun_prop) e he
    (-β * Real.exp (-β * diagonalExpectationValue T hT e))
    (diagonalExpectationValue T hT e) rfl (fun x => exp_tangent β _ x)

end

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
## Equality cases for the Peierls–Bogoliubov inequality

This file isolates the strict scalar and finite weighted-sum steps needed to reverse the
tangent-line proof of the Peierls–Bogoliubov inequality for the Gibbs weight
`x ↦ exp (-β x)`.
-/

/-- For nonzero `β`, the tangent line to `x ↦ exp (-β x)` at `x₀` lies strictly below the
exponential away from `x₀`. -/
theorem exp_tangent_strict (β x₀ x : ℝ) (hβ : β ≠ 0) (hx : x ≠ x₀) :
    (-β * Real.exp (-β * x₀)) * x +
        (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀) <
      Real.exp (-β * x) := by
  have harg_ne : -β * (x - x₀) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hβ) (sub_ne_zero.mpr hx)
  have hexp_ne : Real.exp (-β * (x - x₀)) ≠ 1 := by
    intro h
    apply harg_ne
    apply Real.exp_injective
    simpa using h
  have hlog := Real.log_lt_sub_one_of_pos
    (Real.exp_pos (-β * (x - x₀))) hexp_ne
  rw [Real.log_exp] at hlog
  have hexp : Real.exp (-β * x) =
      Real.exp (-β * x₀) * Real.exp (-β * (x - x₀)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hmul := mul_lt_mul_of_pos_left hlog (Real.exp_pos (-β * x₀))
  nlinarith

/-- For nonzero `β`, equality with the tangent line occurs exactly at the tangency point. -/
theorem exp_tangent_eq_iff (β x₀ x : ℝ) (hβ : β ≠ 0) :
    (-β * Real.exp (-β * x₀)) * x +
        (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀) =
      Real.exp (-β * x) ↔ x = x₀ := by
  constructor
  · intro heq
    by_contra hx
    exact (ne_of_lt (exp_tangent_strict β x₀ x hβ hx)) heq
  · rintro rfl
    ring

/-- Equality between a finite nonnegative weighted sum of exponential values and the corresponding
weighted tangent values forces every point with positive weight to be the tangency point. -/
theorem exp_tangent_weighted_sum_eq_support
    {ι : Type*} [Fintype ι] (β x₀ : ℝ) (hβ : β ≠ 0)
    (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (heq :
      ∑ i, w i *
          ((-β * Real.exp (-β * x₀)) * E i +
            (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) =
        ∑ i, w i * Real.exp (-β * E i)) :
    ∀ i, 0 < w i → E i = x₀ := by
  have hgap_nonneg (i : ι) :
      0 ≤ Real.exp (-β * E i) -
        ((-β * Real.exp (-β * x₀)) * E i +
          (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) :=
    sub_nonneg.mpr (exp_tangent β x₀ (E i))
  have hsumzero :
      ∑ i, w i *
          (Real.exp (-β * E i) -
            ((-β * Real.exp (-β * x₀)) * E i +
              (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀))) = 0 := by
    calc
      _ = (∑ i, w i * Real.exp (-β * E i)) -
          ∑ i, w i *
            ((-β * Real.exp (-β * x₀)) * E i +
              (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := sub_eq_zero.mpr heq.symm
  have htermzero : ∀ i, w i *
      (Real.exp (-β * E i) -
        ((-β * Real.exp (-β * x₀)) * E i +
          (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀))) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j) (hgap_nonneg j))).mp hsumzero i (Finset.mem_univ i)
  intro i hwi
  have hgapzero :
      Real.exp (-β * E i) -
        ((-β * Real.exp (-β * x₀)) * E i +
          (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) = 0 :=
    (mul_eq_zero.mp (htermzero i)).resolve_left hwi.ne'
  apply (exp_tangent_eq_iff β x₀ (E i) hβ).mp
  linarith

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

omit [FiniteDimensional ℂ H] in
/-- In finite dimension, the lossless diagonal expectation of a self-adjoint operator is the
weighted sum of the eigenvalues in any supplied orthonormal eigenbasis, with squared basis
coordinates as weights. -/
private theorem diagonalExpectationValue_eq_sum_orthonormal_eigenbasis
    {ι : Type*} [Fintype ι] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (b : OrthonormalBasis ι ℂ H) (E : ι → ℝ)
    (hE : ∀ i, (T : H →ₗ[ℂ] H) (b i) = (E i : ℂ) • b i) (x : H) :
    diagonalExpectationValue T hT x =
      ∑ i, E i * ‖b.repr x i‖ ^ 2 := by
  have hcoord (i : ι) : b.repr (T x) i = (E i : ℂ) * b.repr x i := by
    calc
      b.repr (T x) i = inner ℂ (b i) (T x) := b.repr_apply_apply (T x) i
      _ = inner ℂ (T (b i)) x := (hT.isSymmetric (b i) x).symm
      _ = inner ℂ ((E i : ℂ) • b i) x := by
        apply congrArg (fun y : H => inner ℂ y x)
        exact hE i
      _ = (E i : ℂ) * inner ℂ (b i) x := by
        rw [inner_smul_left]
        simp
      _ = (E i : ℂ) * b.repr x i := by rw [b.repr_apply_apply]
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue]
  have hinner := b.repr.inner_map_map (T x) x
  rw [PiLp.inner_apply] at hinner
  rw [← hinner]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord i]
  change
    inner ℂ ((E i : ℂ) * b.repr x i) (b.repr x i) =
      (E i : ℂ) * (‖b.repr x i‖ : ℂ) ^ 2
  rw [show (E i : ℂ) * b.repr x i = (E i : ℂ) • b.repr x i from rfl]
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp

/-- In finite dimension and for `β ≠ 0`, equality in the Gibbs specialization of the
Peierls–Bogoliubov inequality holds exactly when the unit vector is an eigenvector of the original
self-adjoint operator, with eigenvalue equal to its lossless diagonal expectation. -/
theorem gibbs_peierls_bogoliubov_eq_iff_eigenvector
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (β : ℝ) (hβ : β ≠ 0)
    (e : H) (he : ‖e‖ = 1) :
    (Real.exp (-β * diagonalExpectationValue T hT e) : ℂ) =
        inner ℂ (cfc (R := ℝ) (fun x => Real.exp (-β * x)) T e) e ↔
      (T : H →ₗ[ℂ] H) e = (diagonalExpectationValue T hT e : ℂ) • e := by
  let x₀ : ℝ := diagonalExpectationValue T hT e
  change (Real.exp (-β * x₀) : ℂ) =
      inner ℂ (cfc (R := ℝ) (fun x => Real.exp (-β * x)) T e) e ↔
    (T : H →ₗ[ℂ] H) e = (x₀ : ℂ) • e
  constructor
  · intro heq
    let E : Fin (Module.finrank ℂ H) → ℝ := hT.isSymmetric.eigenvalues rfl
    let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
      hT.isSymmetric.eigenvectorBasis rfl
    let w : Fin (Module.finrank ℂ H) → ℝ := fun i => ‖b.repr e i‖ ^ 2
    let G : H →L[ℂ] H := cfc (R := ℝ) (fun x => Real.exp (-β * x)) T
    let hG : IsSelfAdjoint G := IsSelfAdjoint.cfc (f := fun x : ℝ => Real.exp (-β * x)) (a := T)
    have hTb (i : Fin (Module.finrank ℂ H)) :
        (T : H →ₗ[ℂ] H) (b i) = (E i : ℂ) • b i := by
      simpa [E, b] using hT.isSymmetric.apply_eigenvectorBasis rfl i
    have hGb (i : Fin (Module.finrank ℂ H)) :
        (G : H →ₗ[ℂ] H) (b i) = (Real.exp (-β * E i) : ℂ) • b i := by
      simpa [G] using
        (cfc_apply_eigenvector (T := T) hT (hTb i)
          (f := fun x : ℝ => Real.exp (-β * x)) (by fun_prop))
    have hw_nonneg (i : Fin (Module.finrank ℂ H)) : 0 ≤ w i := by
      exact sq_nonneg _
    have hw_sum : ∑ i, w i = 1 := by
      have hnorm := (EuclideanSpace.norm_sq_eq (b.repr e)).symm
      simpa [w, he] using hnorm
    have hTsum := diagonalExpectationValue_eq_sum_orthonormal_eigenbasis
      T hT b E hTb e
    have hmean : ∑ i, w i * E i = x₀ := by
      calc
        ∑ i, w i * E i = ∑ i, E i * ‖b.repr e i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [w, mul_comm]
        _ = diagonalExpectationValue T hT e := hTsum.symm
        _ = x₀ := rfl
    have hGsum : diagonalExpectationValue G hG e =
        ∑ i, Real.exp (-β * E i) * w i := by
      simpa [w] using
        (diagonalExpectationValue_eq_sum_orthonormal_eigenbasis
          G hG b (fun i => Real.exp (-β * E i)) hGb e)
    have heqG : Real.exp (-β * x₀) = diagonalExpectationValue G hG e := by
      apply Complex.ofReal_injective
      rw [coe_diagonalExpectationValue]
      simpa [G] using heq
    let m : ℝ := -β * Real.exp (-β * x₀)
    let c : ℝ := Real.exp (-β * x₀) - m * x₀
    have hleft : ∑ i, w i * (m * E i + c) = Real.exp (-β * x₀) := by
      calc
        ∑ i, w i * (m * E i + c) =
            ∑ i, (m * (w i * E i) + w i * c) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = m * (∑ i, w i * E i) + (∑ i, w i) * c := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        _ = Real.exp (-β * x₀) := by
          rw [hmean, hw_sum]
          dsimp [m, c]
          ring
    have hright : ∑ i, w i * Real.exp (-β * E i) = Real.exp (-β * x₀) := by
      calc
        ∑ i, w i * Real.exp (-β * E i) =
            ∑ i, Real.exp (-β * E i) * w i := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = diagonalExpectationValue G hG e := hGsum.symm
        _ = Real.exp (-β * x₀) := heqG.symm
    have hweighted :
        ∑ i, w i *
            ((-β * Real.exp (-β * x₀)) * E i +
              (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) =
          ∑ i, w i * Real.exp (-β * E i) := by
      simpa [m, c] using hleft.trans hright.symm
    have hsupport := exp_tangent_weighted_sum_eq_support
      β x₀ hβ w E hw_nonneg hweighted
    apply b.repr.injective
    ext i
    have hcoord := hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl e i
    change b.repr (T e) i = b.repr ((x₀ : ℂ) • e) i
    rw [show b.repr (T e) i = (E i : ℂ) * b.repr e i by
      simpa [E, b] using hcoord]
    simp only [map_smul]
    change (E i : ℂ) * b.repr e i = (x₀ : ℂ) * b.repr e i
    by_cases hcoordzero : b.repr e i = 0
    · simp [hcoordzero]
    · have hwpos : 0 < w i := by
        dsimp [w]
        exact sq_pos_of_pos (norm_pos_iff.mpr hcoordzero)
      rw [hsupport i hwpos]
  · intro heigen
    have hcfc :
        cfc (R := ℝ) (fun x => Real.exp (-β * x)) T e =
          (Real.exp (-β * x₀) : ℂ) • e := by
      exact cfc_apply_eigenvector (T := T) hT heigen
        (f := fun x : ℝ => Real.exp (-β * x)) (by fun_prop)
    rw [hcfc, inner_smul_left, inner_self_eq_norm_sq_to_K, he]
    calc
      (Real.exp (-β * x₀) : ℂ) =
          starRingEnd ℂ (Real.exp (-β * x₀) : ℂ) :=
        (Complex.conj_ofReal (Real.exp (-β * x₀))).symm
      _ = starRingEnd ℂ (Real.exp (-β * x₀) : ℂ) *
          (((1 : ℝ) : ℂ) ^ 2) := by norm_num

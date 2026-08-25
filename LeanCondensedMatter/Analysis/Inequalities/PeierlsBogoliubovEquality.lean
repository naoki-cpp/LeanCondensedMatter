import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubov
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectationFinite
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC

set_option linter.style.header false

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Equality cases for the Peierls–Bogoliubov inequality

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

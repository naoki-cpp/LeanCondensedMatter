import LeanCondensedMatter.Analysis.Dyson.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Basic

set_option linter.style.header false

/-!
# Unitarity of Dyson evolution

For a self-adjoint interaction `V(t)` and a skew-adjoint scalar coupling `c`, the bounded Dyson
evolution is unitary on every compact nonnegative interval where the continuity and boundedness
hypotheses hold.

The proof uses the Volterra equation and the existing vector-valued Grönwall uniqueness argument.
-/

namespace Dyson

open Set

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- A Dyson evolution with self-adjoint interaction and skew-adjoint scalar coupling satisfies
`U(t)† U(t) = 1`. -/
theorem star_mul_evolution_eq_one_of_star_eq
    {V : ℝ → A} (hVstar : ∀ s, star (V s) = V s)
    (lam : ℂ) (hlam : star lam = -lam)
    {β M t : ℝ} (hβ : 0 ≤ β)
    (h : ContinuousBoundedInteraction V β M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    star (evolution V lam t) * evolution V lam t = 1 := by
  let U : ℝ → A := fun s => evolution V lam s
  let q : ℝ → A := fun s => star (U s) * U s - 1
  have hUcont : ContinuousOn U (Icc (0 : ℝ) β) := by
    simpa [U] using continuousOn_evolution_of_bound h lam
  have hUEq : ∀ s ∈ Icc (0 : ℝ) β,
      U s = 1 - lam • ∫ u in (0 : ℝ)..s, V u * U u := by
    intro s hs
    simpa [U] using evolution_eq_one_sub_integral_of_bound h hs lam
  have hUderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt U (-(lam • (V s * U s))) (Ici s) s := by
    intro s hs
    exact hasDerivWithinAt_of_volterra h.interaction_continuous hβ hs lam hUcont hUEq
  have hqcont : ContinuousOn q (Icc (0 : ℝ) β) := by
    exact (hUcont.star.mul hUcont).sub continuousOn_const
  have hqderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt q 0 (Ici s) s := by
    intro s hs
    have hUd := hUderiv s hs
    have hprod := hUd.star.mul hUd
    have hsub := hprod.sub_const (1 : A)
    have hzero :
        star (-(lam • (V s * U s))) * U s +
            star (U s) * -(lam • (V s * U s)) = 0 := by
      simp [hlam, hVstar s, star_smul, star_mul, mul_assoc]
    rw [hzero] at hsub
    simpa [q] using hsub
  have hq0 : q 0 = 0 := by
    simp [q, U, evolution_zero]
  have hqbound : ∀ s ∈ Ico (0 : ℝ) β,
      ‖(0 : A)‖ ≤ 0 * ‖q s‖ := by
    simp
  have hqzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := q) (f' := fun _ => (0 : A)) (K := 0)
    (a := (0 : ℝ)) (b := β) hqcont hqderiv hq0 hqbound
  have := hqzero t ht
  simpa [q, U, sub_eq_zero] using this

/-- A Dyson evolution with self-adjoint interaction and skew-adjoint scalar coupling satisfies
`U(t) U(t)† = 1`. -/
theorem mul_star_evolution_eq_one_of_star_eq
    {V : ℝ → A} (hVstar : ∀ s, star (V s) = V s)
    (lam : ℂ) (hlam : star lam = -lam)
    {β M t : ℝ} (hβ : 0 ≤ β)
    (h : ContinuousBoundedInteraction V β M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    evolution V lam t * star (evolution V lam t) = 1 := by
  let U : ℝ → A := fun s => evolution V lam s
  let q : ℝ → A := fun s => U s * star (U s) - 1
  let q' : ℝ → A := fun s => lam • (q s * V s - V s * q s)
  have hUcont : ContinuousOn U (Icc (0 : ℝ) β) := by
    simpa [U] using continuousOn_evolution_of_bound h lam
  have hUEq : ∀ s ∈ Icc (0 : ℝ) β,
      U s = 1 - lam • ∫ u in (0 : ℝ)..s, V u * U u := by
    intro s hs
    simpa [U] using evolution_eq_one_sub_integral_of_bound h hs lam
  have hUderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt U (-(lam • (V s * U s))) (Ici s) s := by
    intro s hs
    exact hasDerivWithinAt_of_volterra h.interaction_continuous hβ hs lam hUcont hUEq
  have hqcont : ContinuousOn q (Icc (0 : ℝ) β) := by
    exact (hUcont.mul hUcont.star).sub continuousOn_const
  have hqderiv : ∀ s ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt q (q' s) (Ici s) s := by
    intro s hs
    have hUd := hUderiv s hs
    have hprod := hUd.mul hUd.star
    have hsub := hprod.sub_const (1 : A)
    have hstar :
        star (-(lam • (V s * U s))) = lam • (star (U s) * V s) := by
      simp [hlam, hVstar s, star_smul, star_mul]
    have hcomm :
        -(lam • (V s * U s)) * star (U s) +
            U s * star (-(lam • (V s * U s))) = q' s := by
      rw [hstar]
      simp only [q', q]
      noncomm_ring
      module
    rw [hcomm] at hsub
    simpa [q] using hsub
  have hq0 : q 0 = 0 := by
    simp [q, U, evolution_zero]
  have hqbound : ∀ s ∈ Ico (0 : ℝ) β,
      ‖q' s‖ ≤ (2 * ‖lam‖ * M) * ‖q s‖ := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) β := ⟨hs.1, hs.2.le⟩
    rw [show q' s = lam • (q s * V s - V s * q s) by rfl, norm_smul]
    calc
      ‖lam‖ * ‖q s * V s - V s * q s‖ ≤
          ‖lam‖ * (‖q s * V s‖ + ‖V s * q s‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖lam‖ * (‖q s‖ * M + M * ‖q s‖) := by
        gcongr
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left
              (h.interaction_norm_le s hsIcc) (norm_nonneg _))
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right
              (h.interaction_norm_le s hsIcc) (norm_nonneg _))
      _ = (2 * ‖lam‖ * M) * ‖q s‖ := by ring
  have hqzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := q) (f' := q') (K := 2 * ‖lam‖ * M)
    (a := (0 : ℝ)) (b := β) hqcont hqderiv hq0 hqbound
  have := hqzero t ht
  simpa [q, U, sub_eq_zero] using this

/-- The two unitary identities for a self-adjoint Dyson interaction with skew-adjoint coupling. -/
theorem evolution_unitary_relations_of_star_eq
    {V : ℝ → A} (hVstar : ∀ s, star (V s) = V s)
    (lam : ℂ) (hlam : star lam = -lam)
    {β M t : ℝ} (hβ : 0 ≤ β)
    (h : ContinuousBoundedInteraction V β M)
    (ht : t ∈ Icc (0 : ℝ) β) :
    star (evolution V lam t) * evolution V lam t = 1 ∧
      evolution V lam t * star (evolution V lam t) = 1 :=
  ⟨star_mul_evolution_eq_one_of_star_eq hVstar lam hlam hβ h ht,
    mul_star_evolution_eq_one_of_star_eq hVstar lam hlam hβ h ht⟩

end
end Dyson

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Full-angle cosine moments

The full-period real cosine moments and their reduction, parity, factorial, and norm
identities are purely analytic. They do not depend on physical momentum,
transport normalization, or the Fourier--Bessel kernel representation.
-/

namespace AngularHarmonics

noncomputable section

open MeasureTheory
open scoped Interval

/-- The real cosine moment over a full polar revolution. Its explicit even moments
are the coefficients in the Fourier--Bessel expansion of the zeroth kernel. -/
noncomputable def fullAngleCosineMoment (n : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ n

@[simp] theorem fullAngleCosineMoment_zero :
    fullAngleCosineMoment 0 = 2 * Real.pi := by
  simp [fullAngleCosineMoment]

@[simp] theorem fullAngleCosineMoment_one :
    fullAngleCosineMoment 1 = 0 := by
  simp [fullAngleCosineMoment]

/-- The full-period cosine moments satisfy the standard reduction formula. -/
theorem fullAngleCosineMoment_add_two (n : ℕ) :
    fullAngleCosineMoment (n + 2) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * fullAngleCosineMoment n := by
  simpa [fullAngleCosineMoment] using
    (integral_cos_pow (a := (0 : ℝ)) (b := 2 * Real.pi) n)

/-- Closed finite-product formula for every even full-angle cosine moment. -/
theorem fullAngleCosineMoment_even (n : ℕ) :
    fullAngleCosineMoment (2 * n) =
      (2 * Real.pi) *
        ∏ k ∈ Finset.range n, ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hindex : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hindex, fullAngleCosineMoment_add_two, ih, Finset.prod_range_succ]
      push_cast
      ring

/-- The even full-angle cosine moment in factorial form, ready for the
coefficient comparison with Mathlib's regularized hypergeometric Bessel series. -/
theorem fullAngleCosineMoment_even_factorial (n : ℕ) :
    fullAngleCosineMoment (2 * n) =
      (2 * Real.pi) * (Nat.factorial (2 * n) : ℝ) / ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by
  rw [fullAngleCosineMoment_even]
  have hprod (n : ℕ) :
      (∏ k ∈ Finset.range n, ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2))) =
        (Nat.factorial (2 * n) : ℝ) / ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hfac2 :
            (Nat.factorial (2 * (n + 1)) : ℝ) =
              (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (Nat.factorial (2 * n) : ℝ) := by
          have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
          rw [hindex, Nat.factorial_succ, Nat.factorial_succ]
          push_cast
          ring
        have hfacn : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        rw [Finset.prod_range_succ, ih, hfac2, hfacn, pow_succ]
        have hfact : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hpow : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
        have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
        have hsucc : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hfact, hpow, hden, hsucc]
        ring
  rw [hprod]
  ring

/-- Every odd full-angle cosine moment vanishes. -/
@[simp] theorem fullAngleCosineMoment_odd (n : ℕ) :
    fullAngleCosineMoment (2 * n + 1) = 0 := by
  induction n with
  | zero => simpa using fullAngleCosineMoment_one
  | succ n ih =>
      have hindex : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [hindex, fullAngleCosineMoment_add_two, ih, mul_zero]

/-- A full-period cosine moment is bounded by the length of its integration interval. -/
theorem fullAngleCosineMoment_norm_le (n : ℕ) :
    ‖fullAngleCosineMoment n‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ => Real.cos θ ^ n) (by
      intro θ _
      simp only [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ))
  simpa only [fullAngleCosineMoment, one_mul, sub_zero,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
    using h

end
end AngularHarmonics

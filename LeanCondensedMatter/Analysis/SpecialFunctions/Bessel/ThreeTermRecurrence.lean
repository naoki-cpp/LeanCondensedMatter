import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Three-term recurrence for complex Bessel J functions

The order-zero/one/two recurrence follows from a regularized hypergeometric
coefficient identity. It holds at all complex arguments, including the origin.
A related real-argument product identity is derived without dividing the
recurrence by the argument. No Fourier transform or transport data is required.
-/

namespace BesselHypergeometric

noncomputable section

/-- The adjacent bottom-parameter regularized hypergeometric series obey the
coefficient-shift relation needed for the Bessel recurrence of orders zero to two. -/
private theorem regularizedHGFun_one_sub_two_eq_mul_three (w : ℂ) :
    Complex.regularizedHGFun 0 {(1 : ℂ)} w -
      Complex.regularizedHGFun 0 {(2 : ℂ)} w =
        w * Complex.regularizedHGFun 0 {(3 : ℂ)} w := by
  let c1 : ℕ → ℂ := Complex.regularizedHGFunCoeff 0 {(1 : ℂ)}
  let c2 : ℕ → ℂ := Complex.regularizedHGFunCoeff 0 {(2 : ℂ)}
  let c3 : ℕ → ℂ := Complex.regularizedHGFunCoeff 0 {(3 : ℂ)}
  have hcoeff (n : ℕ) : c1 (n + 1) - c2 (n + 1) = c3 n := by
    dsimp only [c1, c2, c3]
    have h0 := regularizedHGFunCoeff_zero_singleton_nat_add_one 0 (n + 1)
    have h1 := regularizedHGFunCoeff_zero_singleton_nat_add_one 1 (n + 1)
    have h2 := regularizedHGFunCoeff_zero_singleton_nat_add_one 2 n
    norm_num only [Nat.add_zero] at h0 h1 h2
    rw [h0, h1, h2, ← pow_two]
    simp only [Nat.factorial_succ]
    push_cast
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    have hf : (Nat.factorial n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hn2' : (2 : ℂ) + (n : ℂ) ≠ 0 := by simpa [add_comm] using hn2
    field_simp [hn2']
    rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
    field_simp [hn2]
    ring
  have hzero : c1 0 = c2 0 := by
    dsimp only [c1, c2]
    have h0 := regularizedHGFunCoeff_zero_singleton_nat_add_one 0 0
    have h1 := regularizedHGFunCoeff_zero_singleton_nat_add_one 1 0
    norm_num at h0 h1
    rw [h0, h1]
  have hs1 : Summable (fun n : ℕ => c1 n * w ^ n) := by
    simpa only [c1, Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      (Complex.regularizedHGFunSeries 0 {(1 : ℂ)}).summable (by simp)
  have hs2 : Summable (fun n : ℕ => c2 n * w ^ n) := by
    simpa only [c2, Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      (Complex.regularizedHGFunSeries 0 {(2 : ℂ)}).summable (by simp)
  have hseries (b : Multiset ℂ) :
      Complex.regularizedHGFun 0 b w =
        ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 b n * w ^ n := by
    rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
      ← FormalMultilinearSeries.ofScalarsSum,
      FormalMultilinearSeries.ofScalars_sum_eq]
    simp only [smul_eq_mul]
  rw [hseries {(1 : ℂ)}, hseries {(2 : ℂ)}, hseries {(3 : ℂ)}]
  change (∑' n : ℕ, c1 n * w ^ n) -
      (∑' n : ℕ, c2 n * w ^ n) =
        w * ∑' n : ℕ, c3 n * w ^ n
  calc
    (∑' n : ℕ, c1 n * w ^ n) - (∑' n : ℕ, c2 n * w ^ n) =
        ∑' n : ℕ, (c1 n * w ^ n - c2 n * w ^ n) :=
      (hs1.tsum_sub hs2).symm
    _ = ∑' n : ℕ, w * (c3 n * w ^ n) := by
      rw [(hs1.sub hs2).tsum_eq_zero_add]
      simp only [pow_zero, mul_one, hzero, sub_self, zero_add]
      apply tsum_congr
      intro n
      rw [← sub_mul, hcoeff]
      ring
    _ = w * ∑' n : ℕ, c3 n * w ^ n := by
      rw [tsum_mul_left]

/-- The Bessel three-term recurrence at orders zero, one, and two.
This is formulated without dividing by the argument, so it includes the origin. -/
theorem besselJ_zero_one_two_recurrence (z : ℂ) :
    2 * Complex.besselJ 1 z =
      z * (Complex.besselJ 0 z + Complex.besselJ 2 z) := by
  let w : ℂ := -(z / 2) ^ 2
  have h := regularizedHGFun_one_sub_two_eq_mul_three w
  have h0 : Complex.besselJ 0 z =
      Complex.regularizedHGFun 0 {(1 : ℂ)} w := by
    simp [Complex.besselJ_def, w]
  have h1 : Complex.besselJ 1 z =
      (z / 2) * Complex.regularizedHGFun 0 {(2 : ℂ)} w := by
    change (z / 2) ^ (1 : ℂ) *
      Complex.regularizedHGFun 0 {((1 : ℂ) + 1)} (-(z / 2) ^ 2) = _
    simp only [Complex.cpow_one, one_add_one_eq_two]
    rfl
  have h2 : Complex.besselJ 2 z =
      (z / 2) ^ 2 * Complex.regularizedHGFun 0 {(3 : ℂ)} w := by
    change (z / 2) ^ (2 : ℂ) *
      Complex.regularizedHGFun 0 {((2 : ℂ) + 1)} (-(z / 2) ^ 2) = _
    have ha : (2 : ℂ) + 1 = 3 := by norm_num
    rw [ha, Complex.cpow_two]
  rw [h0, h1, h2]
  dsimp [w] at h
  calc
    2 * ((z / 2) * Complex.regularizedHGFun 0 {(2 : ℂ)} (-(z / 2) ^ 2)) =
        z * Complex.regularizedHGFun 0 {(2 : ℂ)} (-(z / 2) ^ 2) := by ring
    _ = z * (Complex.regularizedHGFun 0 {(1 : ℂ)} (-(z / 2) ^ 2) -
        (-(z / 2) ^ 2) * Complex.regularizedHGFun 0 {(3 : ℂ)} (-(z / 2) ^ 2)) := by
      rw [show Complex.regularizedHGFun 0 {(2 : ℂ)} (-(z / 2) ^ 2) =
          Complex.regularizedHGFun 0 {(1 : ℂ)} (-(z / 2) ^ 2) -
            (-(z / 2) ^ 2) * Complex.regularizedHGFun 0 {(3 : ℂ)} (-(z / 2) ^ 2) by
        linear_combination -h]
    _ = z * (Complex.regularizedHGFun 0 {(1 : ℂ)} (-(z / 2) ^ 2) +
        (z / 2) ^ 2 * Complex.regularizedHGFun 0 {(3 : ℂ)} (-(z / 2) ^ 2)) := by
      ring

/-- The Bessel recurrence eliminates the apparent singularity of J₁(z)²/z
at the origin, with the convention that division by zero is zero. -/
theorem besselJ_one_sq_div_eq_half_product (z : ℝ) :
    Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ) =
      Complex.besselJ 1 (z : ℂ) *
        (Complex.besselJ 0 (z : ℂ) + Complex.besselJ 2 (z : ℂ)) / 2 := by
  by_cases hz : z = 0
  · subst z
    simp [Complex.besselJ_zero]
  · have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
    apply (div_eq_iff hzc).2
    have hrec := besselJ_zero_one_two_recurrence (z : ℂ)
    linear_combination (Complex.besselJ 1 (z : ℂ) / 2) * hrec

end
end BesselHypergeometric

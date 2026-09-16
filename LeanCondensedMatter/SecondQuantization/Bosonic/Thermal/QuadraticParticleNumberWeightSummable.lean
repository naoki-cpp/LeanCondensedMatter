import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Summability of quadratic particle-number-weighted bosonic Gibbs weights

Quartic bosonic matrix coefficients grow at most quadratically in occupation numbers.  This module
keeps the degree-two public API while delegating the analytic finite-mode Gibbs majorant to
`PolynomialOccupationWeightSummable`.  The square estimate is a direct monomial specialization;
the mixed product follows from those square specializations by the elementary quadratic bound.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- A square occupation-number weight remains summable against the free bosonic Boltzmann weight. -/
theorem summable_particleNumber_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    Summable (fun n : Occupation Mode => (n j : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  classical
  have h := summable_occupationMonomial_boltzmannWeight ε β hpos
    (fun i => if i = j then 2 else 0)
  refine h.congr fun n => ?_
  congr 1
  rw [Fintype.prod_eq_single j]
  · simp
  · intro i hij
    simp [hij]

/-- A product of two occupation numbers remains summable against the free bosonic Boltzmann weight.
This is the degree-two estimate needed for diagonal matrix coefficients of quartic interactions. -/
theorem summable_particleNumber_mul_particleNumber_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (i j : Mode) :
    Summable (fun n : Occupation Mode =>
      (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
  have hi := summable_particleNumber_sq_boltzmannWeight ε β hpos i
  have hj := summable_particleNumber_sq_boltzmannWeight ε β hpos j
  have hmajorant : Summable (fun n : Occupation Mode =>
      (1 / 2 : ℝ) *
        ((n i : ℝ) ^ 2 * boltzmannWeight ε β n +
          (n j : ℝ) ^ 2 * boltzmannWeight ε β n)) := by
    exact (hi.add hj).mul_left (1 / 2 : ℝ)
  apply hmajorant.of_norm_bounded
  intro n
  have hni : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  have hnj : 0 ≤ (n j : ℝ) := Nat.cast_nonneg _
  have hw : 0 ≤ boltzmannWeight ε β n := by
    exact Real.exp_nonneg _
  have hab : (n i : ℝ) * (n j : ℝ) ≤ ((n i : ℝ) ^ 2 + (n j : ℝ) ^ 2) / 2 := by
    nlinarith [sq_nonneg ((n i : ℝ) - (n j : ℝ))]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hni hnj) hw)]
  calc
    (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n ≤
        (((n i : ℝ) ^ 2 + (n j : ℝ) ^ 2) / 2) * boltzmannWeight ε β n :=
      mul_le_mul_of_nonneg_right hab hw
    _ = (1 / 2 : ℝ) *
        ((n i : ℝ) ^ 2 * boltzmannWeight ε β n +
          (n j : ℝ) ^ 2 * boltzmannWeight ε β n) := by ring

end
end Bosonic
end SecondQuantization

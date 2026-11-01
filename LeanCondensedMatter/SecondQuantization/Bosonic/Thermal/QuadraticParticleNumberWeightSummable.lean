import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Summability of quadratic particle-number-weighted bosonic Gibbs weights

Quartic bosonic matrix coefficients grow at most quadratically in occupation numbers.  This module
keeps the degree-two public API while delegating the analytic finite-mode Gibbs majorant to
`PolynomialOccupationWeightSummable`. The mixed product is a monomial with one exponent contribution
from each selected mode; the square estimate specializes it to two equal modes.
The total-particle-number square then follows by summing those mixed mode-pair estimates.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- A product of two occupation numbers remains summable against the free bosonic Boltzmann weight.
This is the degree-two estimate needed for diagonal matrix coefficients of quartic interactions. -/
theorem summable_particleNumber_mul_particleNumber_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (i j : Mode) :
    Summable (fun n : Occupation Mode =>
      (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
  classical
  have h := summable_shiftedOccupationPowerProduct_boltzmannWeight ε β hpos (fun _ => 0)
    (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
  refine h.congr fun n => ?_
  simp only [Nat.add_zero, pow_add, Finset.prod_mul_distrib]
  congr 1
  have hprod (k : Mode) :
      (∏ l : Mode, (n l : ℝ) ^ (if l = k then 1 else 0 : ℕ)) = (n k : ℝ) := by
    rw [Fintype.prod_eq_single k]
    · simp
    · intro l hl
      simp [hl]
  rw [hprod i, hprod j]

/-- A square occupation-number weight remains summable against the free bosonic Boltzmann weight. -/
theorem summable_particleNumber_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    Summable (fun n : Occupation Mode => (n j : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  simpa only [pow_two] using
    summable_particleNumber_mul_particleNumber_boltzmannWeight ε β hpos j j

/-! ## Total particle number -/

/-- The square of the total particle number remains summable against the free bosonic Boltzmann
weight.  This is the uniform degree-two majorant used for quartic ladder amplitudes. -/
theorem summable_particleNumber_total_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      (particleNumber n : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  have hinner : ∀ i : Mode, Summable (fun n : Occupation Mode =>
      ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    intro i
    exact summable_sum fun j (_ : j ∈ Finset.univ) =>
      summable_particleNumber_mul_particleNumber_boltzmannWeight ε β hpos i j
  have hdouble : Summable (fun n : Occupation Mode =>
      ∑ i, ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    exact summable_sum fun i (_ : i ∈ Finset.univ) => hinner i
  refine hdouble.congr fun n => ?_
  rw [particleNumber_eq_sum_univ]
  push_cast
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_mul]

end
end Bosonic
end SecondQuantization

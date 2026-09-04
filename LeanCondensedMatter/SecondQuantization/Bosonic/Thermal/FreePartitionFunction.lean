import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# The one-mode free bosonic partition series

For a mode of energy `ε` at inverse temperature `β`, the occupation number ranges over `ℕ`. Its
Boltzmann weights form the geometric series
`Σ k, exp (-β k ε) = (1 - exp (-β ε))⁻¹`, summable exactly when `0 < β ε`.

This module is independent of the bosonic Fock-space and time-evolution constructions. Multi-mode
weights and their product formula are built on it in the subsequent thermal modules.
-/

namespace SecondQuantization
namespace Bosonic

/-- The one-mode bosonic Boltzmann weight `e^{-βkε}`. -/
noncomputable def oneModeBoltzmannWeight (β ε : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) * (-β * ε))

/-- The one-mode Boltzmann series sums to the geometric-series value when `0 < βε`. -/
theorem hasSum_oneModeBoltzmannWeight {β ε : ℝ} (h : 0 < β * ε) :
    HasSum (oneModeBoltzmannWeight β ε) (1 - Real.exp (-β * ε))⁻¹ := by
  have hnorm : ‖Real.exp (-β * ε)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have hgeo := hasSum_geometric_of_norm_lt_one hnorm
  unfold oneModeBoltzmannWeight
  simpa only [Real.exp_nat_mul] using hgeo

/-- The one-mode Boltzmann series is summable exactly when `0 < βε`. -/
theorem summable_oneModeBoltzmannWeight_iff {β ε : ℝ} :
    Summable (oneModeBoltzmannWeight β ε) ↔ 0 < β * ε := by
  unfold oneModeBoltzmannWeight
  simp_rw [Real.exp_nat_mul]
  rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

end Bosonic
end SecondQuantization

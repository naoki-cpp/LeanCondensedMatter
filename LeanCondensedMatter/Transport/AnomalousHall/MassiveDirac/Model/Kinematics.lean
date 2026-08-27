import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial kinematics of the two-dimensional massive Dirac model

This file owns radial dispersion facts shared by longitudinal response and the Bastin radial-energy
bridge.  These facts depend only on the clean massive-Dirac spectrum; occupation and transport
relaxation enter downstream.

For

```text
E(p) = sqrt(v^2 p^2 + m^2),
```

the radial derivative away from a zero-energy degeneracy is

```text
dE/dp = v^2 p / E(p).
```
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- The positive Dirac energy is nonnegative for every momentum. -/
theorem energy_nonneg (v m px py : ℝ) :
    0 ≤ energy v m px py := by
  exact Real.sqrt_nonneg _

/-- For nonnegative mass, the massive-Dirac energy is bounded below by the mass uniformly in
momentum. -/
theorem mass_le_energy (v m px py : ℝ) (_hm : 0 ≤ m) :
    m ≤ energy v m px py := by
  have hkin : 0 ≤ v ^ 2 * (px ^ 2 + py ^ 2) := by
    positivity
  have hsq : m ^ 2 ≤ energy v m px py ^ 2 := by
    rw [energy_sq]
    unfold energySq
    linarith
  have hE := energy_nonneg v m px py
  nlinarith [_hm]

/-- For positive mass the model stays uniformly away from the Dirac degeneracy. -/
theorem energy_pos_of_mass_pos (v m px py : ℝ) (hm : 0 < m) :
    0 < energy v m px py := by
  exact lt_of_lt_of_le hm (mass_le_energy v m px py hm.le)

/-- Radial derivative of the positive massive-Dirac energy. -/
def radialEnergyDerivative (v m p : ℝ) : ℝ :=
  v ^ 2 * p / energy v m p 0

/-- The positive radial massive-Dirac dispersion has derivative `v² p / E` when `m > 0`. -/
theorem hasDerivAt_energy_radial
    (v m p : ℝ) (hm : 0 < m) :
    HasDerivAt (fun q : ℝ => energy v m q 0) (radialEnergyDerivative v m p) p := by
  have hpow : HasDerivAt (fun q : ℝ => q ^ 2) (2 * p) p := by
    simpa using (hasDerivAt_id p).pow 2
  have hmul :
      HasDerivAt (fun q : ℝ => v ^ 2 * q ^ 2) (v ^ 2 * (2 * p)) p := by
    exact HasDerivAt.const_mul (v ^ 2) hpow
  have hpoly :
      HasDerivAt (fun q : ℝ => energySq v m q 0) (v ^ 2 * (2 * p)) p := by
    have hadd := hmul.add (hasDerivAt_const p (m ^ 2))
    simpa [energySq] using hadd
  have hsq_ne : energySq v m p 0 ≠ 0 := by
    unfold energySq
    positivity
  have hsqrt := hpoly.sqrt hsq_ne
  unfold radialEnergyDerivative energy
  convert hsqrt using 1
  field_simp [ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)]

/-- The radial energy derivative is continuous for positive mass. -/
theorem continuous_radialEnergyDerivative
    (v m : ℝ) (hm : 0 < m) :
    Continuous (radialEnergyDerivative v m) := by
  unfold radialEnergyDerivative
  have hE : Continuous (fun p : ℝ => energy v m p 0) := by
    unfold energy energySq
    fun_prop
  exact (continuous_const.mul continuous_id).div hE
    (fun p => ne_of_gt (energy_pos_of_mass_pos v m p 0 hm))

end

end AnomalousHall.MassiveDirac

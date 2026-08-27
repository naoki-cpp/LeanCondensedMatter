import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Longitudinal kinematics of the two-dimensional massive Dirac model

This file owns radial dispersion facts shared by longitudinal response and the Bastin radial-energy
bridge.  The starting point remains the clean dispersion and the occupation-derived Fermi radius;
no relaxation time or finite DC conductivity is introduced here.

For

```text
E(p) = sqrt(v^2 p^2 + m^2),
```

the radial derivative away from a zero-energy degeneracy is

```text
dE/dp = v^2 p / E(p).
```

At the metallic Fermi radius this gives the squared Fermi-surface speed factor

```text
v_F^2 = v^2 * (1 - m^2 / epsilon_F^2).
```

A downstream longitudinal-response layer may combine this kinematic factor with an explicit
transport lifetime or finite-broadening theorem.  This file does not identify the clean metallic
DC conductivity with a finite number.
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
  have hpoly :
      HasDerivAt (fun q : ℝ => energySq v m q 0) (v ^ 2 * (2 * p)) p := by
    simpa [energySq] using
      (((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).add_const (m ^ 2)
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

/-- At the occupation-derived metallic Fermi radius, the squared radial energy derivative has the
standard massive-Dirac Fermi-surface form
`v^2 * (1 - m^2 / epsilon_F^2)`. -/
theorem radialEnergyDerivative_sq_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) ^ 2 =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) := by
  have hfermiPos : 0 < fermiEnergy := lt_of_lt_of_le hm hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  unfold radialEnergyDerivative
  rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF]
  rw [div_pow, mul_pow,
    metallicFermiRadius_sq v m fermiEnergy hm hmF]
  field_simp [hfermiNe, hv]

/-- In the strictly metallic regime `0 < m < epsilon_F`, the squared Fermi-surface radial
derivative is strictly positive when `v ≠ 0`. -/
theorem radialEnergyDerivative_sq_metallicFermiRadius_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) ^ 2 := by
  rw [radialEnergyDerivative_sq_metallicFermiRadius v m fermiEnergy hv hm hmF.le]
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_pos (lt_trans hm hmF)
  have hmSqLt : m ^ 2 < fermiEnergy ^ 2 := by
    nlinarith
  have hratio : m ^ 2 / fermiEnergy ^ 2 < 1 := by
    exact (div_lt_one hfermiSq).2 hmSqLt
  positivity

end

end AnomalousHall.MassiveDirac

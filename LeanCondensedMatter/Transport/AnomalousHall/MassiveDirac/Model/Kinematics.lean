import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Occupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Longitudinal kinematics of the two-dimensional massive Dirac model

This file records the radial energy-slope data needed by a later longitudinal-conductivity
benchmark.  The starting point remains the clean dispersion and the occupation-derived Fermi
radius; no relaxation time or finite DC conductivity is introduced here.

For

```text
E(p) = sqrt(v^2 p^2 + m^2),
```

the radial energy slope away from a zero-energy degeneracy has the closed form

```text
v^2 p / E(p).
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

/-- Closed radial slope of the positive massive-Dirac energy,
`dE/dp = v^2 p / E(p)` wherever the positive energy is nonzero.

The present definition packages the algebraic expression used by longitudinal kinematics; later
response theorems remain responsible for any relaxation-time or Kubo interpretation. -/
def radialEnergySlope (v m p : ℝ) : ℝ :=
  v ^ 2 * p / energy v m p 0

/-- At the occupation-derived metallic Fermi radius, the squared radial energy slope has the
standard massive-Dirac Fermi-surface form
`v^2 * (1 - m^2 / epsilon_F^2)`. -/
theorem radialEnergySlope_sq_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    radialEnergySlope v m (metallicFermiRadius v m fermiEnergy) ^ 2 =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) := by
  have hfermiPos : 0 < fermiEnergy := lt_of_lt_of_le hm hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  unfold radialEnergySlope
  rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF]
  rw [div_pow, mul_pow,
    metallicFermiRadius_sq v m fermiEnergy hm hmF]
  field_simp [hfermiNe, hv]
  ring

/-- In the strictly metallic regime `0 < m < epsilon_F`, the squared Fermi-surface radial slope is
strictly positive when `v ≠ 0`. -/
theorem radialEnergySlope_sq_metallicFermiRadius_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < radialEnergySlope v m (metallicFermiRadius v m fermiEnergy) ^ 2 := by
  rw [radialEnergySlope_sq_metallicFermiRadius v m fermiEnergy hv hm hmF.le]
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_pos (lt_trans hm hmF)
  have hmSqLt : m ^ 2 < fermiEnergy ^ 2 := by
    nlinarith
  have hratio : m ^ 2 / fermiEnergy ^ 2 < 1 := by
    exact (div_lt_one hfermiSq).2 hmSqLt
  positivity

end

end AnomalousHall.MassiveDirac

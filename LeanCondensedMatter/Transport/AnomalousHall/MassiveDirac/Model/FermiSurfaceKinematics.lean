import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Occupation

set_option linter.style.header false

/-!
# Fermi-surface kinematics of the two-dimensional massive Dirac model

This file combines the clean radial kinematics with the occupation-derived metallic Fermi radius.
It contains no relaxation-time or conductivity assumption.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Isotropic full-angle mean square of the `x` group-velocity component evaluated at the explicit
upper-band Fermi radius. -/
def isotropicFermiSurfaceMeanSquareVelocityX (v m fermiEnergy : ℝ) : ℝ :=
  isotropicMeanSquareRadialGroupVelocityX v m (metallicFermiRadius v m fermiEnergy)

/-- In the positive-mass metallic-or-band-edge regime, the isotropic Fermi-surface factor is

`<v_x²>_FS = (v² / 2) * (1 - m² / ε_F²)`.

The factor `1/2` comes from the full-circle angular average proved in `Model.Kinematics`. -/
theorem isotropicFermiSurfaceMeanSquareVelocityX_eq
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) / 2 := by
  unfold isotropicFermiSurfaceMeanSquareVelocityX
  rw [isotropicMeanSquareRadialGroupVelocityX_eq,
    radialEnergyDerivative_sq_metallicFermiRadius v m fermiEnergy hv hm hmF]

/-- In the strictly metallic regime `0 < m < ε_F`, the isotropic Fermi-surface `v_x²` factor is
strictly positive when `v ≠ 0`. -/
theorem isotropicFermiSurfaceMeanSquareVelocityX_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m < fermiEnergy) :
    0 < isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy := by
  unfold isotropicFermiSurfaceMeanSquareVelocityX
  rw [isotropicMeanSquareRadialGroupVelocityX_eq]
  exact div_pos
    (radialEnergyDerivative_sq_metallicFermiRadius_pos v m fermiEnergy hv hm hmF)
    (by norm_num)

end

end AnomalousHall.MassiveDirac

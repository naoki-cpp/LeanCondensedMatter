import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Occupation
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-temperature relaxation-time longitudinal conductivity benchmark

This file introduces the first finite longitudinal electrical-conductivity benchmark for the
metallic two-dimensional massive Dirac model.  The Fermi-surface kinematics are exact consequences
of the clean spectrum, while the positive transport lifetime `τ_tr` is an explicit phenomenological
input of the relaxation-time approximation.  This benchmark supplies one scalar `τ_tr` outside the
Fermi-surface angular average, so it assumes that the transport lifetime is uniform around the
isotropic Fermi circle.  An angle-dependent lifetime would instead require the Fermi-surface average
of `v_x² τ_tr(θ)`.

The Fermi-level state-count factor is not inserted as a closed formula.  It is defined from the
isotropic Fermi-circle Jacobian in the physical-momentum convention,

```text
D_F = [1 / (2πℏ)^2] * [2π p_F / |dE/dp|_F],
```

and is then reduced to the standard massive-Dirac expression.  At zero temperature, where the
longitudinal intraband weight is supported on the Fermi surface, the finite benchmark is

```text
σxx^RTA = e^2 D_F <v_x^2>_FS τ_tr.
```

No self-energy, single-particle lifetime, vertex correction, or exact clean DC conductivity is
identified with `τ_tr` in this module.  A finite-temperature extension must replace the sharp
Fermi-surface factor by the appropriate energy integral weighted by the occupation derivative.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Upper-band Fermi-surface density-of-states factor from the isotropic radial Jacobian in the
physical-momentum measure `d²p/(2πℏ)²`.

The definition is total as a real-valued expression.  Its density-of-states interpretation and
closed form below use the strict metallic regime, where the Fermi circle and radial derivative are
nonzero. -/
def upperBandFermiSurfaceDensityOfStates
    (hbar v m fermiEnergy : ℝ) : ℝ :=
  momentumMeasurePrefactor hbar *
    (2 * Real.pi * metallicFermiRadius v m fermiEnergy /
      |radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy)|)

/-- In the strict metallic regime `|m| < ε_F`, the Fermi-circle Jacobian gives the single-cone
upper-band DOS

`D_F = ε_F / (2π ℏ² v²)`.
-/
theorem upperBandFermiSurfaceDensityOfStates_eq
    (hbar v m fermiEnergy : ℝ) (hhbar : hbar ≠ 0) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    upperBandFermiSurfaceDensityOfStates hbar v m fermiEnergy =
      fermiEnergy / (2 * Real.pi * hbar ^ 2 * v ^ 2) := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hplus : 0 < fermiEnergy + |m| :=
    add_pos_of_pos_of_nonneg hfermiPos (abs_nonneg m)
  have hprod : 0 < (fermiEnergy - |m|) * (fermiEnergy + |m|) :=
    mul_pos (sub_pos.mpr hmF) hplus
  have hgap : 0 < fermiEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith
  have hpFSq : 0 < metallicFermiRadius v m fermiEnergy ^ 2 := by
    rw [metallicFermiRadius_sq v m fermiEnergy hmF.le]
    exact div_pos hgap (sq_pos_of_ne_zero hv)
  have hpFne : metallicFermiRadius v m fermiEnergy ≠ 0 := by
    intro hzero
    rw [hzero] at hpFSq
    norm_num at hpFSq
  have hpFpos : 0 < metallicFermiRadius v m fermiEnergy :=
    lt_of_le_of_ne (metallicFermiRadius_nonneg v m fermiEnergy) (Ne.symm hpFne)
  have hderivpos :
      0 < radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) := by
    unfold radialEnergyDerivative
    rw [energy_metallicFermiRadius v m fermiEnergy hv hmF.le]
    exact div_pos (mul_pos (sq_pos_of_ne_zero hv) hpFpos) hfermiPos
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold upperBandFermiSurfaceDensityOfStates momentumMeasurePrefactor
  rw [abs_of_pos hderivpos]
  unfold radialEnergyDerivative
  rw [energy_metallicFermiRadius v m fermiEnergy hv hmF.le]
  field_simp [hhbar, hv, hpFne, hfermiNe, hpi]

/-- Zero-temperature Fermi-surface relaxation-time-approximation benchmark for the longitudinal
electrical conductivity.

The supplied `transportLifetime` is `τ_tr`, a positive current-relaxation time assumed uniform around
the isotropic Fermi circle, which is why it multiplies the angularly averaged `v_x²` as one scalar.
This definition does not claim that `τ_tr` follows from the clean Hamiltonian or from a self-energy
broadening. -/
def zeroTemperatureRelaxationTimeLongitudinalConductivity
    (e hbar v m fermiEnergy : ℝ)
    (transportLifetime : PositiveTransportLifetime) : ℝ :=
  e ^ 2 * upperBandFermiSurfaceDensityOfStates hbar v m fermiEnergy *
    isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy *
      transportLifetime.lifetime

/-- Closed single-cone zero-temperature massive-Dirac relaxation-time benchmark

`σxx^RTA = e² τ_tr (ε_F² - m²) / (4π ℏ² ε_F)`.
-/
theorem zeroTemperatureRelaxationTimeLongitudinalConductivity_eq
    (e hbar v m fermiEnergy : ℝ)
    (transportLifetime : PositiveTransportLifetime)
    (hhbar : hbar ≠ 0) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    zeroTemperatureRelaxationTimeLongitudinalConductivity
        e hbar v m fermiEnergy transportLifetime =
      e ^ 2 * transportLifetime.lifetime * (fermiEnergy ^ 2 - m ^ 2) /
        (4 * Real.pi * hbar ^ 2 * fermiEnergy) := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  unfold zeroTemperatureRelaxationTimeLongitudinalConductivity
  rw [upperBandFermiSurfaceDensityOfStates_eq hbar v m fermiEnergy hhbar hv hmF,
    isotropicFermiSurfaceMeanSquareVelocityX_eq v m fermiEnergy hv hmF.le hfermiNe]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hhbar, hv, hfermiNe, hpi]
  ring

/-- With nonzero charge and nonzero `ℏ`, the finite zero-temperature RTA longitudinal conductivity
is positive in the strict metallic regime. -/
theorem zeroTemperatureRelaxationTimeLongitudinalConductivity_pos
    (e hbar v m fermiEnergy : ℝ)
    (transportLifetime : PositiveTransportLifetime)
    (he : e ≠ 0) (hhbar : hbar ≠ 0) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    0 < zeroTemperatureRelaxationTimeLongitudinalConductivity
      e hbar v m fermiEnergy transportLifetime := by
  rw [zeroTemperatureRelaxationTimeLongitudinalConductivity_eq
    e hbar v m fermiEnergy transportLifetime hhbar hv hmF]
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hplus : 0 < fermiEnergy + |m| :=
    add_pos_of_pos_of_nonneg hfermiPos (abs_nonneg m)
  have hprod : 0 < (fermiEnergy - |m|) * (fermiEnergy + |m|) :=
    mul_pos (sub_pos.mpr hmF) hplus
  have hgap : 0 < fermiEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith
  have hden : 0 < 4 * Real.pi * hbar ^ 2 * fermiEnergy := by
    have hhbarSq : 0 < hbar ^ 2 := sq_pos_of_ne_zero hhbar
    positivity
  exact div_pos
    (mul_pos (mul_pos (sq_pos_of_ne_zero he) transportLifetime.lifetime_pos) hgap)
    hden

end

end QuantumTheory.Transport.Models.MassiveDirac

import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceRadialKernel
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialEnergyBridge
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Closed radial energy kernel for the massive-Dirac Středa surface term

The two radial interband ordered pairs must be combined before the clean limit is taken. Their
source-pole pieces cancel algebraically, leaving one real Fermi-shell kernel. This file derives that
closed kernel and transports the radial momentum integral to the positive-energy coordinate.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport

/-- Sum of the retarded and advanced scalar resolvents with the same real offset. -/
theorem inv_add_I_add_inv_sub_I_eq_real
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ +
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (((2 * offset / (broadening ^ 2 + offset ^ 2) : ℝ) : ℂ)) := by
  have hplus : (offset : ℂ) + (broadening : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have him : broadening = 0 := by
      simpa using congrArg Complex.im hzero
    exact hbroadening him
  have hminus : (offset : ℂ) - (broadening : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have him : broadening = 0 := by
      simpa using congrArg Complex.im hzero
    exact hbroadening him
  have hsumReal : broadening ^ 2 + offset ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hsumPow : (broadening : ℂ) ^ 2 + (offset : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hsumReal
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  push_cast
  field_simp [hplus, hminus, hsumPow]
  ring_nf
  rw [hI]
  ring

/-- Radial opposite-source Středa surface block expressed through its target-centered Lorentzian and
regular radial spectator. -/
theorem stredaSurfaceBandPairContribution_opposite_source_radial_eq
    (band : Band) (e v m p fermiEnergy broadening : ℝ)
    (hE : energy v m p 0 ≠ 0) (hbroadening : broadening ≠ 0) :
    stredaSurfaceBandPairContribution (oppositeBand band) band
        e v m p 0 fermiEnergy broadening =
      Complex.I *
        (lorentzianSpectralKernel
          (fermiEnergy - bandEnergy band v m p 0) broadening : ℂ) *
        (((((interbandEnergyGap band v m p 0 +
                (fermiEnergy - bandEnergy band v m p 0) : ℝ) : ℂ) +
              (broadening : ℂ) * Complex.I)⁻¹) +
          ((((interbandEnergyGap band v m p 0 +
                (fermiEnergy - bandEnergy band v m p 0) : ℝ) : ℂ) -
              (broadening : ℂ) * Complex.I)⁻¹)) *
          radialInterbandCurrentAmplitude band e v m p := by
  have hpair := stredaSurfaceBandPairContribution_opposite_source_targetCentered
    band e v m p 0 (fermiEnergy - bandEnergy band v m p 0) broadening hbroadening
  have hspectator := targetCenteredStredaSurfaceSpectatorCurrentFactor_radial_eq
    band e v m p (fermiEnergy - bandEnergy band v m p 0) broadening hE
  calc
    stredaSurfaceBandPairContribution (oppositeBand band) band
        e v m p 0 fermiEnergy broadening =
      stredaSurfaceBandPairContribution (oppositeBand band) band
        e v m p 0
          (bandEnergy band v m p 0 +
            (fermiEnergy - bandEnergy band v m p 0)) broadening := by
          congr 1
          ring
    _ = Complex.I *
        (lorentzianSpectralKernel
          (fermiEnergy - bandEnergy band v m p 0) broadening : ℂ) *
        targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m p 0
          (fermiEnergy - bandEnergy band v m p 0, broadening) := hpair
    _ = _ := by
      rw [hspectator]
      ring

/-- Closed real radial interband Středa surface kernel at Fermi energy `fermiEnergy`. -/
def radialInterbandStredaSurfaceKernel
    (e v m fermiEnergy energy broadening : ℝ) : ℝ :=
  -4 * e ^ 2 * m * v ^ 2 * broadening /
    (((fermiEnergy + energy) ^ 2 + broadening ^ 2) *
      ((fermiEnergy - energy) ^ 2 + broadening ^ 2))

/-- The sum of the two radial interband Středa surface blocks is exactly the real closed kernel.
Combining the two ordered pairs before taking `η → 0⁺` removes the apparent source-pole
singularities. -/
theorem interbandStredaSurfaceTraceContribution_radial_eq_kernel
    (e v m p fermiEnergy broadening : ℝ)
    (hE : energy v m p 0 ≠ 0) (hbroadening : 0 < broadening) :
    interbandStredaSurfaceTraceContribution
        e v m p 0 fermiEnergy broadening =
      (radialInterbandStredaSurfaceKernel
        e v m fermiEnergy (energy v m p 0) broadening : ℂ) := by
  have hu := stredaSurfaceBandPairContribution_opposite_source_radial_eq
    .upper e v m p fermiEnergy broadening hE hbroadening.ne'
  have hl := stredaSurfaceBandPairContribution_opposite_source_radial_eq
    .lower e v m p fermiEnergy broadening hE hbroadening.ne'
  have hsumPlus := inv_add_I_add_inv_sub_I_eq_real
    (fermiEnergy + energy v m p 0) broadening hbroadening.ne'
  have hsumMinus := inv_add_I_add_inv_sub_I_eq_real
    (fermiEnergy - energy v m p 0) broadening hbroadening.ne'
  have hEc : (((energy v m p 0 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hdenPlus :
      (fermiEnergy + energy v m p 0) ^ 2 + broadening ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hbroadening]
  have hdenMinus :
      (fermiEnergy - energy v m p 0) ^ 2 + broadening ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hbroadening]
  unfold interbandStredaSurfaceTraceContribution
  rw [show stredaSurfaceBandPairContribution .lower .upper
        e v m p 0 fermiEnergy broadening =
      stredaSurfaceBandPairContribution (oppositeBand .upper) .upper
        e v m p 0 fermiEnergy broadening by rfl,
    show stredaSurfaceBandPairContribution .upper .lower
        e v m p 0 fermiEnergy broadening =
      stredaSurfaceBandPairContribution (oppositeBand .lower) .lower
        e v m p 0 fermiEnergy broadening by rfl,
    hu, hl]
  simp only [interbandEnergyGap_eq, bandEnergy, bandSign,
    radialInterbandCurrentAmplitude]
  rw [show 2 * (1 : ℝ) * energy v m p 0 +
        (fermiEnergy - 1 * energy v m p 0) =
      fermiEnergy + energy v m p 0 by ring,
    show 2 * (-1 : ℝ) * energy v m p 0 +
        (fermiEnergy - (-1) * energy v m p 0) =
      fermiEnergy - energy v m p 0 by ring,
    hsumPlus, hsumMinus]
  unfold lorentzianSpectralKernel radialInterbandStredaSurfaceKernel
  push_cast
  field_simp [hEc, hdenPlus, hdenMinus]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by
    rw [pow_two, Complex.I_mul_I]]
  ring

/-- Positive-energy-coordinate Středa surface density after removing the radial Jacobian. -/
def stredaSurfaceRadialEnergyDensity
    (e m fermiEnergy energy broadening : ℝ) : ℝ :=
  -4 * e ^ 2 * m * energy * broadening /
    (((fermiEnergy + energy) ^ 2 + broadening ^ 2) *
      ((fermiEnergy - energy) ^ 2 + broadening ^ 2))

/-- Multiplication by the radial Jacobian is exactly the energy-coordinate density times `dE/dp`.
-/
theorem radialInterbandStredaSurfaceKernel_mul_p_eq_energyDensity_mul_deriv
    (e v m fermiEnergy p broadening : ℝ) (hm : 0 < m) :
    p * radialInterbandStredaSurfaceKernel
        e v m fermiEnergy (energy v m p 0) broadening =
      stredaSurfaceRadialEnergyDensity
          e m fermiEnergy (energy v m p 0) broadening *
        radialEnergyDerivative v m p := by
  have hE : energy v m p 0 ≠ 0 :=
    ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)
  unfold radialInterbandStredaSurfaceKernel stredaSurfaceRadialEnergyDensity
    radialEnergyDerivative
  field_simp [hE]

/-- At nonzero broadening the positive-energy Středa surface density is continuous. -/
theorem continuous_stredaSurfaceRadialEnergyDensity
    (e m fermiEnergy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (stredaSurfaceRadialEnergyDensity e m fermiEnergy · broadening) := by
  have hplus : Continuous
      (fun energy : ℝ => (fermiEnergy + energy) ^ 2 + broadening ^ 2) := by
    fun_prop
  have hminus : Continuous
      (fun energy : ℝ => (fermiEnergy - energy) ^ 2 + broadening ^ 2) := by
    fun_prop
  have hplusNe : ∀ energy : ℝ,
      (fermiEnergy + energy) ^ 2 + broadening ^ 2 ≠ 0 := by
    intro energy
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hminusNe : ∀ energy : ℝ,
      (fermiEnergy - energy) ^ 2 + broadening ^ 2 ≠ 0 := by
    intro energy
    nlinarith [sq_pos_of_ne_zero hbroadening]
  unfold stredaSurfaceRadialEnergyDensity
  exact
    (by fun_prop : Continuous (fun energy : ℝ => -4 * e ^ 2 * m * energy * broadening)).div
      (hplus.mul hminus) (fun energy => mul_ne_zero (hplusNe energy) (hminusNe energy))

/-- Finite positive-energy Středa surface integral. -/
def finiteEnergyStredaSurfaceIntegral
    (e m fermiEnergy energyMax broadening : ℝ) : ℝ :=
  ∫ energy in m..energyMax,
    stredaSurfaceRadialEnergyDensity e m fermiEnergy energy broadening

/-- The radial interband surface integral equals the corresponding positive-energy integral for
positive mass and nonzero broadening. -/
theorem finiteRadialInterbandStredaSurfaceIntegral_eq_energyIntegral
    (e v m fermiEnergy pMax broadening : ℝ)
    (hm : 0 < m) (hpMax : 0 ≤ pMax) (hbroadening : broadening ≠ 0) :
    (∫ p in (0 : ℝ)..pMax,
      p * radialInterbandStredaSurfaceKernel
        e v m fermiEnergy (energy v m p 0) broadening) =
      finiteEnergyStredaSurfaceIntegral
        e m fermiEnergy (energy v m pMax 0) broadening := by
  have hfun :
      (fun p : ℝ =>
        p * radialInterbandStredaSurfaceKernel
          e v m fermiEnergy (energy v m p 0) broadening) =
      (fun p : ℝ =>
        stredaSurfaceRadialEnergyDensity
            e m fermiEnergy (energy v m p 0) broadening *
          radialEnergyDerivative v m p) := by
    funext p
    exact radialInterbandStredaSurfaceKernel_mul_p_eq_energyDensity_mul_deriv
      e v m fermiEnergy p broadening hm
  rw [hfun]
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := pMax)
    (f := fun p : ℝ => energy v m p 0)
    (f' := radialEnergyDerivative v m)
    (g := stredaSurfaceRadialEnergyDensity e m fermiEnergy · broadening)
    (fun p _ => hasDerivAt_energy_radial v m p hm)
    (continuous_radialEnergyDerivative v m hm).continuousOn
    (continuous_stredaSurfaceRadialEnergyDensity
      e m fermiEnergy broadening hbroadening).continuousOn
  have hsub' :
      (∫ p in (0 : ℝ)..pMax,
        stredaSurfaceRadialEnergyDensity e m fermiEnergy (energy v m p 0) broadening *
          radialEnergyDerivative v m p) =
        ∫ energy in energy v m 0 0..energy v m pMax 0,
          stredaSurfaceRadialEnergyDensity e m fermiEnergy energy broadening := by
    simpa only [Function.comp_apply] using hsub
  rw [hsub']
  unfold finiteEnergyStredaSurfaceIntegral
  have hzero : energy v m 0 0 = m := by
    unfold energy energySq
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hm]
  rw [hzero]

end

end AnomalousHall.MassiveDirac

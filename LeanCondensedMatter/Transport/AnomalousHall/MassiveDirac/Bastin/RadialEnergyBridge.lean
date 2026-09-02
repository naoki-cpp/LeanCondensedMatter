import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialDominatedConvergence
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.CleanConductivity
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Kinematics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial momentum-to-energy bridge for the clean Bastin pair

The dominated-convergence theorem for the finite-broadening pair is formulated in radial momentum
`p`, while the existing clean intrinsic Hall benchmark is formulated in the positive Dirac energy
`ε`.  This file closes that coordinate boundary explicitly.

For positive mass, the radial dispersion never vanishes and

```text
dE/dp = v² p / E,
```

so the clean radial momentum density is exactly the clean energy density multiplied by this
Jacobian.  Mathlib's interval-integral change-of-variables theorem then identifies the two finite
radial integrals without hiding the `p dp = E dE / v²` step.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- The radial clean pair density is the energy-coordinate density times `dE/dp`. -/
theorem radialCleanInterbandBastinPairLimitDensity_eq_energyDensity_mul_deriv
    (band : Band) (e v m p : ℝ) (hm : 0 < m) :
    radialCleanInterbandBastinPairLimitDensity band e v m p =
      cleanInterbandBastinPairRadialEnergyDensity band e m (energy v m p 0) *
        radialEnergyDerivative v m p := by
  have hE : energy v m p 0 ≠ 0 :=
    ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)
  unfold radialCleanInterbandBastinPairLimitDensity
    cleanInterbandBastinPairLimitDensity cleanInterbandBastinPairRadialEnergyDensity
    radialBerryEnergyDensity radialEnergyDerivative
  cases band <;>
    simp [berryCurvature_lower, berryCurvature_upper, bandSign] <;>
    field_simp [hE]

/-- The clean radial energy density is continuous on the positive-energy image of any radial
momentum interval when `m > 0`. -/
theorem continuousOn_cleanInterbandBastinPairRadialEnergyDensity_image
    (band : Band) (e v m pMax : ℝ) (hm : 0 < m) :
    ContinuousOn (cleanInterbandBastinPairRadialEnergyDensity band e m)
      ((fun p : ℝ => energy v m p 0) '' [[(0 : ℝ), pMax]]) := by
  unfold cleanInterbandBastinPairRadialEnergyDensity radialBerryEnergyDensity
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.mul continuousOn_const
  exact continuousOn_id.zpow₀ (-2) (fun x hx => Or.inl <| by
    rcases hx with ⟨p, _, rfl⟩
    exact ne_of_gt (energy_pos_of_mass_pos v m p 0 hm))

/-- The clean radial momentum integral equals the existing positive-energy shell integral.
This is the explicit formal version of `p dp = E dE / v²`. -/
theorem finiteRadialCleanInterbandBastinPairIntegral_eq_energyShell
    (band : Band) (e v m pMax : ℝ) (hm : 0 < m) (hpMax : 0 ≤ pMax) :
    finiteRadialCleanInterbandBastinPairIntegral band e v m pMax =
      cleanInterbandBastinPairEnergyShellIntegral
        band e m m (energy v m pMax 0) := by
  unfold finiteRadialCleanInterbandBastinPairIntegral
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hpMax]
  have hfun :
      (fun p : ℝ => radialCleanInterbandBastinPairLimitDensity band e v m p) =
      (fun p : ℝ =>
        cleanInterbandBastinPairRadialEnergyDensity band e m (energy v m p 0) *
          radialEnergyDerivative v m p) := by
    funext p
    exact radialCleanInterbandBastinPairLimitDensity_eq_energyDensity_mul_deriv
      band e v m p hm
  rw [hfun]
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := pMax)
    (f := fun p : ℝ => energy v m p 0)
    (f' := radialEnergyDerivative v m)
    (g := cleanInterbandBastinPairRadialEnergyDensity band e m)
    (fun p _ => hasDerivAt_energy_radial v m p hm.ne')
    (continuous_radialEnergyDerivative v m hm.ne').continuousOn
    (continuousOn_cleanInterbandBastinPairRadialEnergyDensity_image
      band e v m pMax hm)
  have hsub' :
      (∫ p in (0 : ℝ)..pMax,
        cleanInterbandBastinPairRadialEnergyDensity band e m (energy v m p 0) *
          radialEnergyDerivative v m p) =
        ∫ ε in energy v m 0 0..energy v m pMax 0,
          cleanInterbandBastinPairRadialEnergyDensity band e m ε := by
    simpa only [Function.comp_apply] using hsub
  rw [hsub']
  unfold cleanInterbandBastinPairEnergyShellIntegral
  have hzero : energy v m 0 0 = m := by
    unfold energy energySq
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hm]
  rw [hzero]

end

end AnomalousHall.MassiveDirac

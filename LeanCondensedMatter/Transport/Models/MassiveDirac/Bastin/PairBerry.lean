import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PairIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Berry-curvature form of the massive-Dirac Bastin pair pole limit

The fixed-window interband Bastin-pair theorem already extracts the complete target-band pole at
fixed momentum.  This file identifies the extracted regular factor with the clean Berry-curvature
weight and then takes the real part of the complex Bastin-pair limit.

For a target band `n`, the zero-broadening fixed-window limit is therefore

```text
Re ∫ dE K_Bastin(E, η) → -2π e² Ω_n(p).
```

This remains pointwise in momentum.  No momentum integration or interchange of the momentum
integral with the zero-broadening limit is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- At the target pole, the imaginary part of the regular Bastin spectator/current factor is the
negative physical-current Berry curvature weight. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0)).im =
      -(e ^ 2 * berryCurvature band v m px py) := by
  rw [targetCenteredInterbandSpectatorCurrentFactor_zero]
  have hgap : interbandEnergyGap band v m px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  have hcoeff :
      (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2) =
        ((((interbandEnergyGap band v m px py)⁻¹ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]
  calc
    (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
          bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
        ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
          bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py).im =
        (bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
            bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py).im /
          interbandEnergyGap band v m px py ^ 2 := by
      rw [← mul_sub, hcoeff]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        Complex.sub_im]
      field_simp [hgap]
      ring
    _ = -(e ^ 2 * berryCurvature band v m px py) :=
      bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
        band e v m px py hE

/-- The real part of the extracted interband Bastin pair converges pointwise to
`-2π e² Ω_n(p)`.  This is the local response density that the next momentum-integration slice will
compare with the existing occupied-state Berry integral. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
    (band : Band) (e v m px py radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          band e v m px py radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-2 * Real.pi * (e ^ 2 * berryCurvature band v m px py))) := by
  have hpair :=
    tendsto_targetCenteredInterbandBastinPairIntegral
      band e v m px py radius hE hradiusPos hradius
  have hre :
      Tendsto
        (fun broadening : ℝ =>
          (targetCenteredInterbandBastinPairIntegral
            band e v m px py radius broadening).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((-2 * Complex.I) *
            (Real.pi •
              targetCenteredInterbandSpectatorCurrentFactor
                band e v m px py (0, 0))).re)) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hpair
  have hlimit :
      (((-2 * Complex.I) *
        (Real.pi •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0))).re) =
        -2 * Real.pi * (e ^ 2 * berryCurvature band v m px py) := by
    rw [Complex.mul_re]
    simp [targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
      band e v m px py hE]
    ring
  rw [hlimit] at hre
  exact hre

end

end AnomalousHall.MassiveDirac

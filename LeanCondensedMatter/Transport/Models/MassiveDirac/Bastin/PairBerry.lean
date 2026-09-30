import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PairIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Berry-curvature form of the massive-Dirac Bastin pair pole limit

The fixed-window interband Bastin-pair theorem already extracts the complete target-band pole at
fixed momentum. This file identifies the extracted canonical antisymmetric Hall block with the
clean Berry-curvature weight and then takes the real part of the complex Bastin-pair limit.

For a target band `n`, the zero-broadening fixed-window limit is therefore

```text
Re ∫ dE K_Bastin(E, η) → -2π e² Ω_n(p).
```

This remains pointwise in momentum. No momentum integration or interchange of the momentum
integral with the zero-broadening limit is performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

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
        bastinInterbandBlockDifference 0 1 band e v m px py).im =
      (bastinInterbandBlockDifference 0 1 band e v m px py).im /
        interbandEnergyGap band v m px py ^ 2 := by
      rw [hcoeff]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
      field_simp [hgap]
      ring
    _ = -(e ^ 2 * berryCurvature band v m px py) :=
      bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
        band e v m px py hE

/-- The real part of the extracted interband Bastin pair converges pointwise to
`-2π e² Ω_n(p)`. The analytic real-part pole limit is generic; this specialization supplies only
the massive-Dirac Berry-curvature identification. -/
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
  have hgeneric :=
    tendsto_interbandBastinPoleIntegral_re
      (interbandEnergyGap band v m px py)
      (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
      (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
      radius hradiusPos hradius
  have him :
      (interbandPoleRegularFactor
        (interbandEnergyGap band v m px py)
        (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
        (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
        (0, 0)).im =
      -(e ^ 2 * berryCurvature band v m px py) := by
    rw [← targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor]
    exact targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
      band e v m px py hE
  have hgeneric' : Tendsto
      (fun broadening : ℝ =>
        (interbandBastinPoleIntegral
          (interbandEnergyGap band v m px py)
          (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
          (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
          radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-2 * Real.pi * (e ^ 2 * berryCurvature band v m px py))) := by
    simpa [him] using hgeneric
  refine hgeneric'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  exact congrArg Complex.re
    (targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
      band e v m px py radius broadening hbroadening.ne').symm

end

end QuantumTheory.Transport.Models.MassiveDirac

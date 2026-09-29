import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PairIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Berry-curvature form of the Rashba-exchange Bastin pair pole limit

For a target band `n`, the fixed-window zero-broadening limit of the opposite-source interband
Bastin pair has real part

```text
Re ∫ dE K_Bastin(E, η) → -2π q² Ω_n(p).
```

This remains pointwise in momentum; no momentum integral or limit interchange is performed here.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter

/-- At the target pole, the imaginary part of the regular spectator/current factor is the negative
physical-current Berry-curvature weight. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    (targetCenteredInterbandSpectatorCurrentFactor
      params band px py (0, 0)).im =
      -(params.signedCharge ^ 2 * berryCurvature params band px py) := by
  rw [targetCenteredInterbandSpectatorCurrentFactor_zero]
  have hgap : interbandEnergyGap params band px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero
      params band px py hE
  have hcoeff :
      (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2) =
        ((((interbandEnergyGap params band px py)⁻¹ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]
  calc
    (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2 *
        bastinInterbandBlockDifference params 0 1 band px py).im =
      (bastinInterbandBlockDifference params 0 1 band px py).im /
        interbandEnergyGap params band px py ^ 2 := by
      rw [hcoeff]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
      field_simp [hgap]
      ring
    _ = -(params.signedCharge ^ 2 * berryCurvature params band px py) :=
      bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
        params band px py hE

/-- The real part of the extracted interband Bastin pair converges pointwise to
`-2π q² Ω_n(p)`. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
    (params : Parameters) (band : Band) (px py radius : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap params band px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          params band px py radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-2 * Real.pi *
          (params.signedCharge ^ 2 * berryCurvature params band px py))) := by
  have hpair :=
    tendsto_targetCenteredInterbandBastinPairIntegral
      params band px py radius hE hradiusPos hradius
  have hre :
      Tendsto
        (fun broadening : ℝ =>
          (targetCenteredInterbandBastinPairIntegral
            params band px py radius broadening).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((-2 * Complex.I) *
            (Real.pi •
              targetCenteredInterbandSpectatorCurrentFactor
                params band px py (0, 0))).re)) := by
    simpa [Function.comp_def] using
      Complex.continuous_re.continuousAt.tendsto.comp hpair
  have hlimit :
      (((-2 * Complex.I) *
        (Real.pi •
          targetCenteredInterbandSpectatorCurrentFactor
            params band px py (0, 0))).re) =
        -2 * Real.pi *
          (params.signedCharge ^ 2 * berryCurvature params band px py) := by
    rw [Complex.mul_re]
    simp [targetCenteredInterbandSpectatorCurrentFactor_zero_im_eq_neg_chargeSq_berryCurvature
      params band px py hE]
    ring
  rw [hlimit] at hre
  exact hre

end

end QuantumTheory.Transport.Models.RashbaExchange

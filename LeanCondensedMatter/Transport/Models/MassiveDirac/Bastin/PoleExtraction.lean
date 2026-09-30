import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleContinuity
import LeanCondensedMatter.Transport.Streda.InterbandPole

set_option linter.style.header false

/-!
# Massive-Dirac specialization of generic interband pole extraction

The fixed-window Lorentzian extraction is owned generically by
`Transport.Streda.InterbandPole`. This module preserves the established MassiveDirac API while
specializing that common theorem to the model's interband gap and ordered Hall current blocks.

The result remains pointwise in momentum. No momentum integration or momentum-limit interchange is
performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Lorentzian-weighted target-centered integral of the regular interband spectator/current factor. -/
noncomputable def targetCenteredInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  lorentzianRegularFactorIntegral
    (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
    radius broadening

/-- The model-specific pole integral is the generic isolated-interband regular-factor integral. -/
theorem targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_interbandPoleRegularFactorIntegral
    (band : Band) (e v m px py radius broadening : ℝ) :
    targetCenteredInterbandSpectatorCurrentPoleIntegral
        band e v m px py radius broadening =
      interbandPoleRegularFactorIntegral
        (interbandEnergyGap band v m px py)
        (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
        (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
        radius broadening := by
  unfold targetCenteredInterbandSpectatorCurrentPoleIntegral
    interbandPoleRegularFactorIntegral
  congr 1
  funext p
  exact targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor
    band e v m px py p

/-- On a fixed positive target-centered window narrower than the interband gap, the Lorentzian-
weighted regular spectator/current factor converges to `π` times its target-pole value. -/
theorem tendsto_targetCenteredInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          band e v m px py radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (Real.pi •
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (0, 0))) := by
  have hgeneric :=
    tendsto_interbandPoleRegularFactorIntegral
      (interbandEnergyGap band v m px py)
      (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
      (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
      radius hradiusPos hradius
  have hfun :
      (fun broadening : ℝ =>
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          band e v m px py radius broadening) =
        (fun broadening : ℝ =>
          interbandPoleRegularFactorIntegral
            (interbandEnergyGap band v m px py)
            (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
            (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
            radius broadening) := by
    funext broadening
    exact
      targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_interbandPoleRegularFactorIntegral
        band e v m px py radius broadening
  rw [hfun]
  simpa only [targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor] using
    hgeneric

end

end QuantumTheory.Transport.Models.MassiveDirac

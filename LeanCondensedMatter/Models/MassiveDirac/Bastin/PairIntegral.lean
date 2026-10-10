import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleContinuity
import LeanCondensedMatter.Transport.Streda.InterbandPole
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-window interband Bastin-pair extraction in the massive Dirac model

The target-centered regular-factor integral is shared by the pair factorization and radial
estimates. The concrete ordered band pair is identified with the generic isolated interband Bastin
pole, whose fixed-window zero-broadening limit is provided by `Transport.Streda.InterbandPole`.

The result remains pointwise in momentum. No momentum integration or momentum-limit interchange is
performed here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open Filter QuantumTheory.Transport

/-- Lorentzian-weighted target-centered integral of the regular interband spectator/current factor. -/
noncomputable def targetCenteredInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  lorentzianRegularFactorIntegral
    (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
    radius broadening

/-- The model-specific pole integral is the generic isolated-interband regular-factor integral. -/
private theorem targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_interbandPoleRegularFactorIntegral
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

/-- Fixed target-centered energy-window integral of the interband Bastin Hall pair whose source is
the opposite band and whose target is `band`. -/
noncomputable def targetCenteredInterbandBastinPairIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    bastinBandPairContribution 0 1 (oppositeBand band) band e v m px py
      (bandEnergy band v m px py + offset) broadening

/-- For nonzero broadening, the integrated opposite-source Bastin pair is exactly `-2 i` times the
regular-factor pole integral. -/
theorem targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    (band : Band) (e v m px py radius broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandBastinPairIntegral
        band e v m px py radius broadening =
      (-2 * Complex.I) *
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          band e v m px py radius broadening := by
  unfold targetCenteredInterbandBastinPairIntegral
    targetCenteredInterbandSpectatorCurrentPoleIntegral
    QuantumTheory.Transport.lorentzianRegularFactorIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro offset _
  change
    bastinBandPairContribution 0 1 (oppositeBand band) band e v m px py
        (bandEnergy band v m px py + offset) broadening =
      (-2 * Complex.I) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (offset, broadening))
  rw [bastinBandPairContribution_opposite_source_eq_lorentzian
    0 1 band e v m px py (bandEnergy band v m px py + offset) broadening hbroadening]
  unfold targetCenteredInterbandSpectatorCurrentFactor
  rw [show bandEnergy band v m px py + offset - bandEnergy band v m px py = offset by ring]
  ring

/-- At nonzero broadening, the concrete massive-Dirac pair integral is the generic isolated
interband Bastin pole integral. -/
theorem targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandBastinPairIntegral
        band e v m px py radius broadening =
      interbandBastinPoleIntegral
        (interbandEnergyGap band v m px py)
        (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
        (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
        radius broadening := by
  rw [targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    band e v m px py radius broadening hbroadening]
  unfold interbandBastinPoleIntegral
  rw [targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_interbandPoleRegularFactorIntegral]

end

end QuantumTheory.Models.MassiveDirac

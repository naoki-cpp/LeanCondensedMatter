import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleExtraction
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening extraction of the regular massive-Dirac Bastin pole factor

The regular-factor pole integral is the sum of the vanishing spectator-error integral and the
Lorentzian mass multiplying the target-pole value.  Since the scalar mass tends to `π`, the complete
fixed-window integral extracts `π` times the regular factor at the target pole.

The statement remains pointwise in momentum and uses a fixed positive target-centered energy window
strictly narrower than the interband gap.  No momentum integration or momentum-limit interchange is
performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

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
  have herror :=
    tendsto_targetCenteredInterbandSpectatorCurrentErrorIntegral_zero
      band e v m px py radius hE hradiusPos hradius
  have hmass :=
    tendsto_integral_lorentzianSpectralKernel_symmetric radius hradiusPos
  have hsmulContinuous : ContinuousAt
      (fun mass : ℝ =>
        mass • targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
      Real.pi := by
    fun_prop
  have hmassPole : Tendsto
      (fun broadening : ℝ =>
        (∫ offset in -radius..radius,
          lorentzianSpectralKernel offset broadening) •
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (Real.pi •
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))) := by
    exact hsmulContinuous.tendsto.comp hmass
  have hsum : Tendsto
      (fun broadening : ℝ =>
        targetCenteredInterbandSpectatorCurrentErrorIntegral
            band e v m px py radius broadening +
          (∫ offset in -radius..radius,
            lorentzianSpectralKernel offset broadening) •
            targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (Real.pi •
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))) := by
    simpa using herror.add hmassPole
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hclose := (Metric.tendsto_nhds.1 hsum) ε hε
  have hpositive : ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < broadening := by
    change Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hpositive, hclose] with broadening hbroadening hcloseAt
  rw [targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_error_add_mass_smul_pole
    band e v m px py radius broadening hradiusPos.le hradius hbroadening.ne']
  exact hcloseAt

end

end AnomalousHall.MassiveDirac

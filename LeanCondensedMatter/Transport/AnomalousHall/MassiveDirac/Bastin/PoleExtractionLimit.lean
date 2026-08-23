import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleExtraction
import LeanCondensedMatter.Transport.Analysis.LorentzianPole
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening extraction of the regular massive-Dirac Bastin pole factor

The model-independent Lorentzian regular-factor extraction theorem now lives in
`Transport.Analysis.LorentzianPole`.  This module supplies the massive-Dirac hypotheses: continuity
at the target pole, continuity of fixed-broadening energy slices on a window separated from the
opposite-band pole, and the compact rectangle bound.

The statement remains pointwise in momentum and uses a fixed positive target-centered energy window
strictly narrower than the interband gap.  No momentum integration or momentum-limit interchange is
performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

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
  let factor : ℝ × ℝ → ℂ :=
    targetCenteredInterbandSpectatorCurrentFactor band e v m px py
  have hcontinuous : ContinuousAt factor (0, 0) := by
    simpa [factor] using
      continuousAt_targetCenteredInterbandSpectatorCurrentFactor_zero
        band e v m px py hE
  have hslice : ∀ broadening : ℝ, broadening ≠ 0 →
      ContinuousOn (fun offset : ℝ => factor (offset, broadening))
        (Set.Icc (-radius) radius) := by
    intro broadening _ offset hoffset
    have hfactor :=
      continuousAt_targetCenteredInterbandSpectatorCurrentFactor_on_targetWindow
        band e v m px py radius (offset, broadening) hradius (abs_le.mpr hoffset)
    have hpair : ContinuousAt (fun x : ℝ => (x, broadening)) offset := by
      fun_prop
    have hcomp : ContinuousAt (fun x : ℝ => factor (x, broadening)) offset := by
      change Filter.Tendsto
        (fun x : ℝ =>
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (x, broadening))
        (nhds offset)
        (nhds
          (targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (offset, broadening)))
      exact Filter.Tendsto.comp hfactor hpair
    exact hcomp.continuousWithinAt
  have hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1,
        ‖factor p - factor (0, 0)‖ ≤ C := by
    rcases exists_nonneg_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_le_on_rectangle
        band e v m px py radius 1 hradius with ⟨C, hCnonneg, hC⟩
    refine ⟨C, hCnonneg, ?_⟩
    intro p hp
    simpa [factor, targetCenteredBastinPoleRectangle] using hC p hp
  have hgeneric := tendsto_lorentzianRegularFactorIntegral
    factor radius hradiusPos hcontinuous hslice hbound
  simpa [factor, lorentzianRegularFactorIntegral,
    targetCenteredInterbandSpectatorCurrentPoleIntegral] using hgeneric

end

end AnomalousHall.MassiveDirac

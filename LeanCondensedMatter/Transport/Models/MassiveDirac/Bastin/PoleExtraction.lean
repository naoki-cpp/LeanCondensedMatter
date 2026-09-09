import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleContinuity
import LeanCondensedMatter.Analysis.Lorentzian.Pole
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac specialization of Lorentzian pole extraction

The analytic error decomposition and zero-broadening extraction are owned generically by
`Analysis.Lorentzian.Pole`. This module owns the massive-Dirac fixed-window specialization:
the regular spectator/current pole integral together with its zero-broadening limit.

The limit is pointwise in momentum and uses a fixed positive target-centered energy window strictly
narrower than the interband gap. No model-local error split, duplicate approximate-identity proof,
momentum integration, or momentum-limit interchange is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Lorentzian-weighted target-centered integral of the regular interband spectator/current factor.
This is the massive-Dirac specialization of `lorentzianRegularFactorIntegral`. -/
noncomputable def targetCenteredInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  lorentzianRegularFactorIntegral
    (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
    radius broadening

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
    have hgap : interbandEnergyGap band v m px py ≠ 0 :=
      interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
    simpa [factor] using
      continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
        band e v m px py (0, 0) (by simpa using hgap)
  have hslice : ∀ broadening : ℝ, broadening ≠ 0 →
      ContinuousOn (fun offset : ℝ => factor (offset, broadening))
        (Set.Icc (-radius) radius) := by
    intro broadening _ offset hoffset
    have hshift : interbandEnergyGap band v m px py + offset ≠ 0 :=
      interbandEnergyGap_add_offset_ne_zero_on_targetWindow
        band v m px py offset radius hradius (abs_le.mpr hoffset)
    have hfactor :=
      continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
        band e v m px py (offset, broadening) (by simpa using hshift)
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
    have hcompact : IsCompact (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hfactorContinuous : ContinuousOn factor
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro p hp
      have hshift : interbandEnergyGap band v m px py + p.1 ≠ 0 :=
        interbandEnergyGap_add_offset_ne_zero_on_targetWindow
          band v m px py p.1 radius hradius (abs_le.mpr hp.1)
      exact (continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
        band e v m px py p hshift).continuousWithinAt
    have hconstant : ContinuousOn (fun _ : ℝ × ℝ => factor (0, 0))
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) :=
      continuousOn_const
    rcases hcompact.exists_bound_of_continuousOn (hfactorContinuous.sub hconstant) with ⟨C, hC⟩
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro p hp
    exact le_trans (hC p hp) (le_max_left _ _)
  have hgeneric := tendsto_lorentzianRegularFactorIntegral
    factor radius hradiusPos hcontinuous hslice hbound
  simpa [factor, lorentzianRegularFactorIntegral,
    targetCenteredInterbandSpectatorCurrentPoleIntegral] using hgeneric

end

end QuantumTheory.Transport.Models.MassiveDirac

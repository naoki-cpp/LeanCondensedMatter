import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleContinuity
import LeanCondensedMatter.Analysis.Lorentzian.Pole
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Rashba-exchange specialization of Lorentzian pole extraction

The analytic approximate-identity theorem is owned by `Analysis.Lorentzian.Pole`.  This module
supplies only the Rashba-exchange regular spectator factor on a fixed target-centered energy window
strictly narrower than the interband gap.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter QuantumTheory.Transport

noncomputable def targetCenteredInterbandSpectatorCurrentPoleIntegral
    (params : Parameters) (band : Band) (px py radius broadening : ℝ) : ℂ :=
  lorentzianRegularFactorIntegral
    (targetCenteredInterbandSpectatorCurrentFactor params band px py)
    radius broadening

theorem tendsto_targetCenteredInterbandSpectatorCurrentPoleIntegral
    (params : Parameters) (band : Band) (px py radius : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap params band px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          params band px py radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (Real.pi •
          targetCenteredInterbandSpectatorCurrentFactor
            params band px py (0, 0))) := by
  let factor : ℝ × ℝ → ℂ :=
    targetCenteredInterbandSpectatorCurrentFactor params band px py
  have hcontinuous : ContinuousAt factor (0, 0) := by
    have hgap : interbandEnergyGap params band px py ≠ 0 :=
      interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero
        params band px py hE
    simpa [factor] using
      continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
        params band px py (0, 0) (by simpa using hgap)
  have hslice : ∀ broadening : ℝ, broadening ≠ 0 →
      ContinuousOn (fun offset : ℝ => factor (offset, broadening))
        (Set.Icc (-radius) radius) := by
    intro broadening _ offset hoffset
    have hshift : interbandEnergyGap params band px py + offset ≠ 0 :=
      interbandEnergyGap_add_offset_ne_zero_on_targetWindow
        params band px py offset radius hradius (abs_le.mpr hoffset)
    have hfactor :=
      continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
        params band px py (offset, broadening) (by simpa using hshift)
    have hpair : ContinuousAt (fun x : ℝ => (x, broadening)) offset := by
      fun_prop
    have hcomp : ContinuousAt (fun x : ℝ => factor (x, broadening)) offset := by
      change Filter.Tendsto
        (fun x : ℝ =>
          targetCenteredInterbandSpectatorCurrentFactor
            params band px py (x, broadening))
        (nhds offset)
        (nhds
          (targetCenteredInterbandSpectatorCurrentFactor
            params band px py (offset, broadening)))
      exact Filter.Tendsto.comp hfactor hpair
    exact hcomp.continuousWithinAt
  have hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1,
        ‖factor p - factor (0, 0)‖ ≤ C := by
    have hcompact : IsCompact
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hfactorContinuous : ContinuousOn factor
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro p hp
      have hshift : interbandEnergyGap params band px py + p.1 ≠ 0 :=
        interbandEnergyGap_add_offset_ne_zero_on_targetWindow
          params band px py p.1 radius hradius (abs_le.mpr hp.1)
      exact
        (continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
          params band px py p hshift).continuousWithinAt
    have hconstant : ContinuousOn
        (fun _ : ℝ × ℝ => factor (0, 0))
        (Set.Icc (-radius) radius ×ˢ Set.Icc (0 : ℝ) 1) :=
      continuousOn_const
    rcases hcompact.exists_bound_of_continuousOn
      (hfactorContinuous.sub hconstant) with ⟨C, hC⟩
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro p hp
    exact le_trans (hC p hp) (le_max_left _ _)
  have hgeneric := tendsto_lorentzianRegularFactorIntegral
    factor radius hradiusPos hcontinuous hslice hbound
  simpa [factor, lorentzianRegularFactorIntegral,
    targetCenteredInterbandSpectatorCurrentPoleIntegral] using hgeneric

end

end QuantumTheory.Transport.Models.RashbaExchange

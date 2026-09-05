import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleContinuity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Uniform bounds for the massive-Dirac Bastin spectator on a pole window

The target-centered spectator/current factor is continuous throughout any energy strip whose
radius is smaller than the interband gap. Restricting that strip to a compact rectangle in energy
offset and broadening therefore gives a uniform norm bound.

This file records both the bound on the regular factor itself and the bound on its deviation from
the target-pole value, including a nonnegative choice of the latter bound. These are the compactness
inputs used by the generic Lorentzian pole-extraction theorem.

No energy integration, zero-broadening limit exchange, or momentum integration is performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Compact target-centered rectangle used for a fixed energy window and bounded broadening. -/
def targetCenteredBastinPoleRectangle (radius broadeningMax : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (-radius) radius ×ˢ Set.Icc 0 broadeningMax

/-- The target-centered pole rectangle is compact. -/
theorem isCompact_targetCenteredBastinPoleRectangle
    (radius broadeningMax : ℝ) :
    IsCompact (targetCenteredBastinPoleRectangle radius broadeningMax) := by
  exact isCompact_Icc.prod isCompact_Icc

/-- Every point of the target-centered rectangle lies in the energy strip controlled by the
window-continuity theorem. -/
theorem targetCenteredBastinPoleRectangle_subset_targetStrip
    (radius broadeningMax : ℝ) :
    targetCenteredBastinPoleRectangle radius broadeningMax ⊆
      {p : ℝ × ℝ | |p.1| ≤ radius} := by
  intro p hp
  rcases hp with ⟨hpOffset, _⟩
  exact abs_le.mpr hpOffset

/-- On a target-centered compact rectangle narrower than the interband gap, the regular
spectator/current factor has a uniform norm bound. -/
theorem exists_norm_targetCenteredInterbandSpectatorCurrentFactor_le_on_rectangle
    (band : Band) (e v m px py radius broadeningMax : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    ∃ C : ℝ, ∀ p ∈ targetCenteredBastinPoleRectangle radius broadeningMax,
      ‖targetCenteredInterbandSpectatorCurrentFactor band e v m px py p‖ ≤ C := by
  have hcompact := isCompact_targetCenteredBastinPoleRectangle radius broadeningMax
  have hcontinuous : ContinuousOn
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      (targetCenteredBastinPoleRectangle radius broadeningMax) :=
    (continuousOn_targetCenteredInterbandSpectatorCurrentFactor_targetStrip
      band e v m px py radius hradius).mono
      (targetCenteredBastinPoleRectangle_subset_targetStrip radius broadeningMax)
  exact hcompact.exists_bound_of_continuousOn hcontinuous

/-- The deviation of the regular spectator/current factor from its pole value is also uniformly
bounded on the compact target-centered rectangle. -/
theorem exists_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_le_on_rectangle
    (band : Band) (e v m px py radius broadeningMax : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    ∃ C : ℝ, ∀ p ∈ targetCenteredBastinPoleRectangle radius broadeningMax,
      ‖targetCenteredInterbandSpectatorCurrentFactor band e v m px py p -
        targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0)‖ ≤ C := by
  have hcompact := isCompact_targetCenteredBastinPoleRectangle radius broadeningMax
  have hcontinuous : ContinuousOn
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      (targetCenteredBastinPoleRectangle radius broadeningMax) :=
    (continuousOn_targetCenteredInterbandSpectatorCurrentFactor_targetStrip
      band e v m px py radius hradius).mono
      (targetCenteredBastinPoleRectangle_subset_targetStrip radius broadeningMax)
  have hconstant : ContinuousOn
      (fun _ : ℝ × ℝ =>
        targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0))
      (targetCenteredBastinPoleRectangle radius broadeningMax) :=
    continuousOn_const
  exact hcompact.exists_bound_of_continuousOn (hcontinuous.sub hconstant)

/-- The compact-rectangle deviation bound can be chosen nonnegative. -/
theorem exists_nonneg_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_le_on_rectangle
    (band : Band) (e v m px py radius broadeningMax : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ targetCenteredBastinPoleRectangle radius broadeningMax,
        ‖targetCenteredInterbandSpectatorCurrentFactor band e v m px py p -
          targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0)‖ ≤ C := by
  rcases exists_norm_targetCenteredInterbandSpectatorCurrentFactor_sub_pole_le_on_rectangle
      band e v m px py radius broadeningMax hradius with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  exact le_trans (hC p hp) (le_max_left _ _)

end

end QuantumTheory.Transport.Models.MassiveDirac

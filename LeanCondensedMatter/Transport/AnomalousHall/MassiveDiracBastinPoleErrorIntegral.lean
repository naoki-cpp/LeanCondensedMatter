import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleLocalError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian-weighted error preparation at a massive-Dirac Bastin pole

The target-band Bastin pair factors into a Lorentzian spectral kernel times a regular
spectator/current factor.  Before proving that the weighted spectator error vanishes as the
broadening goes to zero, this file records the scalar positivity/integrability facts and a
nonnegative compact-rectangle bound used in that estimate.

The complete error-integral limit is added only after these ingredients compile against the current
transport API.  No momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- For nonnegative broadening the Lorentzian spectral kernel is nonnegative. -/
theorem lorentzianSpectralKernel_nonneg
    (offset broadening : ℝ) (hbroadening : 0 ≤ broadening) :
    0 ≤ lorentzianSpectralKernel offset broadening :=
  QuantumTheory.Transport.lorentzianSpectralKernel_nonneg
    offset broadening hbroadening

/-- For nonzero broadening the Lorentzian kernel is continuous as a function of energy offset. -/
theorem continuous_lorentzianSpectralKernel_fixed_broadening
    (broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (fun offset : ℝ => lorentzianSpectralKernel offset broadening) := by
  have hden : ∀ offset : ℝ, broadening ^ 2 + offset ^ 2 ≠ 0 := by
    intro offset
    nlinarith [sq_pos_of_ne_zero hbroadening]
  unfold lorentzianSpectralKernel QuantumTheory.Transport.lorentzianSpectralKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2)) hden

/-- At nonzero broadening the Lorentzian kernel is interval integrable on every finite interval. -/
theorem intervalIntegrable_lorentzianSpectralKernel
    (lower upper broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IntervalIntegrable (fun offset : ℝ => lorentzianSpectralKernel offset broadening)
      MeasureTheory.volume lower upper := by
  exact (continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening).intervalIntegrable
    (μ := MeasureTheory.volume) lower upper

/-- The compact-rectangle error bound can always be chosen nonnegative. -/
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

end AnomalousHall.MassiveDirac

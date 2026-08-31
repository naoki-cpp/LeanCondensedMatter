import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weighted Lorentzian windows

This module owns representation-independent facts for multiplying the scalar Lorentzian kernel by a
weight that is locally constant on a centered finite window. Such a weight factors out exactly, and
therefore inherits the `π` symmetric-window mass in the positive zero-broadening limit.

No occupation convention, Hamiltonian, band structure, current operator, or transport observable
appears here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter MeasureTheory

/-- If a weight is constant on the centered integration window, it factors out exactly and the
remaining energy integral is the centered Lorentzian mass. -/
theorem integral_weight_mul_lorentzian_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius broadening : ℝ)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    (∫ energy in center - radius..center + radius,
        weight energy * lorentzianSpectralKernel (energy - center) broadening) =
      value * (∫ offset in -radius..radius,
        lorentzianSpectralKernel offset broadening) := by
  calc
    (∫ energy in center - radius..center + radius,
        weight energy * lorentzianSpectralKernel (energy - center) broadening) =
        ∫ energy in center - radius..center + radius,
          value * lorentzianSpectralKernel (energy - center) broadening := by
      apply intervalIntegral.integral_congr
      intro energy henergy
      change weight energy * lorentzianSpectralKernel (energy - center) broadening =
        value * lorentzianSpectralKernel (energy - center) broadening
      rw [hweight energy henergy]
    _ = ∫ offset in -radius..radius,
        value * lorentzianSpectralKernel offset broadening := by
      let f : ℝ → ℝ := fun offset => value * lorentzianSpectralKernel offset broadening
      have hshift := intervalIntegral.integral_comp_sub_right
        (a := center - radius) (b := center + radius) f center
      rw [show center - radius - center = -radius by ring,
        show center + radius - center = radius by ring] at hshift
      exact hshift
    _ = value * (∫ offset in -radius..radius,
        lorentzianSpectralKernel offset broadening) := by
      rw [intervalIntegral.integral_const_mul]

/-- Local-constant weights inherit the `π` Lorentzian mass in the positive zero-broadening limit. -/
theorem tendsto_integral_weight_mul_lorentzian_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius : ℝ) (hradius : 0 < radius)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          weight energy * lorentzianSpectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (value * Real.pi)) := by
  have hmass := tendsto_integral_lorentzianSpectralKernel_symmetric radius hradius
  have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => value)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds value)).mul hmass
  refine hscaled.congr' ?_
  filter_upwards with broadening
  exact (integral_weight_mul_lorentzian_of_eq_const_on
    weight center value radius broadening hweight).symm

end

end Transport
end QuantumTheory

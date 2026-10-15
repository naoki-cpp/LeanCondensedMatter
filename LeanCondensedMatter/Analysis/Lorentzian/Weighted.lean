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

namespace Lorentzian

noncomputable section

open Filter MeasureTheory

/-- If a weight is constant on the centered integration window, it factors out exactly and the
remaining energy integral is the centered Lorentzian mass. -/
theorem integral_weight_mul_spectralKernel_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius broadening : ℝ)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    (∫ energy in center - radius..center + radius,
        weight energy * spectralKernel (energy - center) broadening) =
      value * (∫ offset in -radius..radius,
        spectralKernel offset broadening) := by
  calc
    (∫ energy in center - radius..center + radius,
        weight energy * spectralKernel (energy - center) broadening) =
        ∫ energy in center - radius..center + radius,
          value * spectralKernel (energy - center) broadening := by
      apply intervalIntegral.integral_congr
      intro energy henergy
      change weight energy * spectralKernel (energy - center) broadening =
        value * spectralKernel (energy - center) broadening
      rw [hweight energy henergy]
    _ = ∫ offset in -radius..radius,
        value * spectralKernel offset broadening := by
      let f : ℝ → ℝ := fun offset => value * spectralKernel offset broadening
      have hshift := intervalIntegral.integral_comp_sub_right
        (a := center - radius) (b := center + radius) f center
      rw [show center - radius - center = -radius by ring,
        show center + radius - center = radius by ring] at hshift
      exact hshift
    _ = value * (∫ offset in -radius..radius,
        spectralKernel offset broadening) := by
      rw [intervalIntegral.integral_const_mul]

/-- Local-constant weights inherit the `π` Lorentzian mass in the positive zero-broadening limit. -/
theorem tendsto_integral_weight_mul_spectralKernel_of_eq_const_on
    (weight : ℝ → ℝ) (center value radius : ℝ) (hradius : 0 < radius)
    (hweight : ∀ energy ∈ Set.uIcc (center - radius) (center + radius),
      weight energy = value) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ energy in center - radius..center + radius,
          weight energy * spectralKernel (energy - center) broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (value * Real.pi)) := by
  have hmass := tendsto_integral_spectralKernel_symmetric radius hradius
  have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => value)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds value)).mul hmass
  refine hscaled.congr' ?_
  filter_upwards with broadening
  exact (integral_weight_mul_spectralKernel_of_eq_const_on
    weight center value radius broadening hweight).symm

end

end Lorentzian

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lorentzian spectral kernel

This module owns the model-independent scalar Lorentzian kernel that appears in retarded-minus-
advanced resolvent differences,

```text
L_η(x) = η / (η² + x²).
```

It proves the elementary scalar resolvent identity, continuity and finite-interval integrability at
nonzero broadening, exact finite-interval integrals, symmetric-window mass bounds and convergence
to `π`, and vanishing mass between fixed nested positive windows as `η → 0⁺`.

No Hamiltonian, band structure, current operator, occupation function, conductivity normalization,
or concrete transport model appears here.
-/

namespace Lorentzian

noncomputable section

open Filter

/-- Real Lorentzian kernel carrying the scalar retarded-minus-advanced spectral weight. -/
def spectralKernel (offset broadening : ℝ) : ℝ :=
  broadening / (broadening ^ 2 + offset ^ 2)

/-- For nonnegative broadening the Lorentzian spectral kernel is nonnegative. -/
theorem spectralKernel_nonneg
    (offset broadening : ℝ) (hbroadening : 0 ≤ broadening) :
    0 ≤ spectralKernel offset broadening := by
  unfold spectralKernel
  positivity

/-- For nonzero broadening the Lorentzian kernel is continuous as a function of energy offset. -/
theorem continuous_spectralKernel_fixed_broadening
    (broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (fun offset : ℝ => spectralKernel offset broadening) := by
  have hden : ∀ offset : ℝ, broadening ^ 2 + offset ^ 2 ≠ 0 := by
    intro offset
    nlinarith [sq_pos_of_ne_zero hbroadening]
  unfold spectralKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2)) hden

/-- At nonzero broadening the Lorentzian kernel is interval integrable on every finite interval. -/
theorem intervalIntegrable_spectralKernel
    (lower upper broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IntervalIntegrable (fun offset : ℝ => spectralKernel offset broadening)
      MeasureTheory.volume lower upper := by
  exact (continuous_spectralKernel_fixed_broadening broadening hbroadening).intervalIntegrable
    (μ := MeasureTheory.volume) lower upper

private theorem complex_offset_add_I_ne_zero
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (offset : ℂ) + (broadening : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact hbroadening him

private theorem complex_offset_sub_I_ne_zero
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (offset : ℂ) - (broadening : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact hbroadening him

/-- Elementary retarded-minus-advanced scalar resolvent identity. -/
theorem inv_add_I_sub_inv_sub_I_eq_spectralKernel
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ -
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (-2 * Complex.I) * (spectralKernel offset broadening : ℂ) := by
  have hplus := complex_offset_add_I_ne_zero offset broadening hbroadening
  have hminus := complex_offset_sub_I_ne_zero offset broadening hbroadening
  have hsumReal : broadening ^ 2 + offset ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hbroadening]
  have hsumPow : (broadening : ℂ) ^ 2 + (offset : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hsumReal
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1 : ℂ) * Complex.I := by rw [hI]
      _ = -Complex.I := by ring
  unfold spectralKernel
  push_cast
  field_simp [hplus, hminus, hsumPow]
  ring_nf
  rw [hI3]
  ring

/-- Exact finite-interval mass of the Lorentzian kernel. -/
theorem integral_spectralKernel
    (lower upper broadening : ℝ) :
    (∫ offset in lower..upper, spectralKernel offset broadening) =
      Real.arctan (upper / broadening) - Real.arctan (lower / broadening) := by
  simpa [spectralKernel, add_comm] using
    (integral_div_sq_add_sq (a := lower) (b := upper) (c := broadening))

/-- On a symmetric interval the Lorentzian mass is `2 arctan(radius / η)`. -/
theorem integral_spectralKernel_symmetric
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius, spectralKernel offset broadening) =
      2 * Real.arctan (radius / broadening) := by
  rw [integral_spectralKernel]
  rw [show (-radius) / broadening = -(radius / broadening) by ring]
  rw [Real.arctan_neg]
  ring

/-- For every fixed positive distance, `arctan(distance / η)` tends to `π / 2` as positive
broadening tends to zero. -/
theorem tendsto_arctan_pos_div_broadening
    (distance : ℝ) (hdistance : 0 < distance) :
    Tendsto
      (fun broadening : ℝ => Real.arctan (distance / broadening))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  have hinv : Tendsto (fun broadening : ℝ => broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hscaled : Tendsto (fun broadening : ℝ => distance * broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => distance)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds distance)).pos_mul_atTop hdistance hinv
  have harctanWithin := Real.tendsto_arctan_atTop.comp hscaled
  have harctan := tendsto_nhds_of_tendsto_nhdsWithin harctanWithin
  change Tendsto
    (fun broadening : ℝ => Real.arctan (distance * broadening⁻¹))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) at harctan
  simpa only [div_eq_mul_inv] using harctan

/-- Every symmetric Lorentzian mass is strictly smaller than `π`. -/
theorem integral_spectralKernel_symmetric_lt_pi
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius,
      spectralKernel offset broadening) < Real.pi := by
  rw [integral_spectralKernel_symmetric]
  linarith [Real.arctan_lt_pi_div_two (radius / broadening)]

/-- Every symmetric Lorentzian mass is at most `π`. -/
theorem integral_spectralKernel_symmetric_le_pi
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius,
      spectralKernel offset broadening) ≤ Real.pi :=
  le_of_lt (integral_spectralKernel_symmetric_lt_pi radius broadening)

/-- Every fixed positive symmetric neighborhood captures asymptotic Lorentzian mass `π` as the
broadening tends to zero from the positive side. -/
theorem tendsto_integral_spectralKernel_symmetric
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, spectralKernel offset broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have harctan := tendsto_arctan_pos_div_broadening radius hradius
  have hmass := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2)).mul harctan
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at hmass
  simpa only [integral_spectralKernel_symmetric] using hmass

/-- Signed difference between the outer and inner symmetric-window Lorentzian masses.
For nonnegative broadening and nested nonnegative radii this is the mass in the two
outer segments; without these conditions it need not be nonnegative. -/
def spectralTailMass (innerRadius outerRadius broadening : ℝ) : ℝ :=
  (∫ offset in -outerRadius..outerRadius,
      spectralKernel offset broadening) -
    (∫ offset in -innerRadius..innerRadius,
      spectralKernel offset broadening)

/-- Exact arctangent form of the symmetric Lorentzian tail mass. -/
theorem spectralTailMass_eq_two_mul_arctan_sub
    (innerRadius outerRadius broadening : ℝ) :
    spectralTailMass innerRadius outerRadius broadening =
      2 * (Real.arctan (outerRadius / broadening) -
        Real.arctan (innerRadius / broadening)) := by
  rw [spectralTailMass,
    integral_spectralKernel_symmetric,
    integral_spectralKernel_symmetric]
  ring

/-- For fixed positive nested radii, all Lorentzian mass between the two windows vanishes as the
broadening tends to zero from the positive side. -/
theorem tendsto_spectralTailMass_zero
    (innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius) (hnested : innerRadius ≤ outerRadius) :
    Tendsto
      (fun broadening : ℝ =>
        spectralTailMass innerRadius outerRadius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have houter : 0 < outerRadius := lt_of_lt_of_le hinner hnested
  have hOuterMass :=
    tendsto_integral_spectralKernel_symmetric outerRadius houter
  have hInnerMass :=
    tendsto_integral_spectralKernel_symmetric innerRadius hinner
  have htail := hOuterMass.sub hInnerMass
  simpa [spectralTailMass] using htail

end

end Lorentzian

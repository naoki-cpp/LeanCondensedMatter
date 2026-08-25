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

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter

/-- Real Lorentzian kernel carrying the scalar retarded-minus-advanced spectral weight. -/
def lorentzianSpectralKernel (offset broadening : ℝ) : ℝ :=
  broadening / (broadening ^ 2 + offset ^ 2)

/-- For nonnegative broadening the Lorentzian spectral kernel is nonnegative. -/
theorem lorentzianSpectralKernel_nonneg
    (offset broadening : ℝ) (hbroadening : 0 ≤ broadening) :
    0 ≤ lorentzianSpectralKernel offset broadening := by
  unfold lorentzianSpectralKernel
  positivity

/-- For nonzero broadening the Lorentzian kernel is continuous as a function of energy offset. -/
theorem continuous_lorentzianSpectralKernel_fixed_broadening
    (broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (fun offset : ℝ => lorentzianSpectralKernel offset broadening) := by
  have hden : ∀ offset : ℝ, broadening ^ 2 + offset ^ 2 ≠ 0 := by
    intro offset
    nlinarith [sq_pos_of_ne_zero hbroadening]
  unfold lorentzianSpectralKernel
  exact continuous_const.div
    ((continuous_const.pow 2).add (continuous_id.pow 2)) hden

/-- At nonzero broadening the Lorentzian kernel is interval integrable on every finite interval. -/
theorem intervalIntegrable_lorentzianSpectralKernel
    (lower upper broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IntervalIntegrable (fun offset : ℝ => lorentzianSpectralKernel offset broadening)
      MeasureTheory.volume lower upper := by
  exact (continuous_lorentzianSpectralKernel_fixed_broadening broadening hbroadening).intervalIntegrable
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
theorem inv_add_I_sub_inv_sub_I_eq_lorentzian
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ -
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (-2 * Complex.I) * (lorentzianSpectralKernel offset broadening : ℂ) := by
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
  unfold lorentzianSpectralKernel
  push_cast
  field_simp [hplus, hminus, hsumPow]
  ring_nf
  rw [hI3]
  ring

/-- Exact finite-interval mass of the Lorentzian kernel. -/
theorem integral_lorentzianSpectralKernel
    (lower upper broadening : ℝ) :
    (∫ offset in lower..upper, lorentzianSpectralKernel offset broadening) =
      Real.arctan (upper / broadening) - Real.arctan (lower / broadening) := by
  simpa [lorentzianSpectralKernel, add_comm] using
    (integral_div_sq_add_sq (a := lower) (b := upper) (c := broadening))

/-- On a symmetric interval the Lorentzian mass is `2 arctan(radius / η)`. -/
theorem integral_lorentzianSpectralKernel_symmetric
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      2 * Real.arctan (radius / broadening) := by
  rw [integral_lorentzianSpectralKernel]
  rw [show (-radius) / broadening = -(radius / broadening) by ring]
  rw [Real.arctan_neg]
  ring

/-- Every symmetric Lorentzian mass is strictly smaller than `π`. -/
theorem integral_lorentzianSpectralKernel_symmetric_lt_pi
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius,
      lorentzianSpectralKernel offset broadening) < Real.pi := by
  rw [integral_lorentzianSpectralKernel_symmetric]
  linarith [Real.arctan_lt_pi_div_two (radius / broadening)]

/-- Every symmetric Lorentzian mass is at most `π`. -/
theorem integral_lorentzianSpectralKernel_symmetric_le_pi
    (radius broadening : ℝ) :
    (∫ offset in -radius..radius,
      lorentzianSpectralKernel offset broadening) ≤ Real.pi :=
  le_of_lt (integral_lorentzianSpectralKernel_symmetric_lt_pi radius broadening)

/-- Every fixed positive symmetric neighborhood captures asymptotic Lorentzian mass `π` as the
broadening tends to zero from the positive side. -/
theorem tendsto_integral_lorentzianSpectralKernel_symmetric
    (radius : ℝ) (hradius : 0 < radius) :
    Tendsto
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds Real.pi) := by
  have hinv : Tendsto (fun broadening : ℝ => broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hscaled : Tendsto (fun broadening : ℝ => radius * broadening⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => radius)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds radius)).pos_mul_atTop hradius hinv
  have harctanWithin := Real.tendsto_arctan_atTop.comp hscaled
  have harctan : Tendsto
      (fun broadening : ℝ => Real.arctan (radius / broadening))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    have h := tendsto_nhds_of_tendsto_nhdsWithin harctanWithin
    change Tendsto
      (fun broadening : ℝ => Real.arctan (radius * broadening⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) at h
    simpa only [div_eq_mul_inv] using h
  have hmass := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2)).mul harctan
  have hfun :
      (fun broadening : ℝ =>
        ∫ offset in -radius..radius, lorentzianSpectralKernel offset broadening) =
      (fun broadening : ℝ => 2 * Real.arctan (radius / broadening)) := by
    funext broadening
    exact integral_lorentzianSpectralKernel_symmetric radius broadening
  have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by
    ring
  rw [hfun]
  rw [hpi] at hmass
  exact hmass

/-- Lorentzian spectral mass between an inner and outer symmetric window, represented as the
outer-window mass minus the inner-window mass. -/
def lorentzianSpectralTailMass (innerRadius outerRadius broadening : ℝ) : ℝ :=
  (∫ offset in -outerRadius..outerRadius,
      lorentzianSpectralKernel offset broadening) -
    (∫ offset in -innerRadius..innerRadius,
      lorentzianSpectralKernel offset broadening)

/-- Exact arctangent form of the symmetric Lorentzian tail mass. -/
theorem lorentzianSpectralTailMass_eq_two_mul_arctan_sub
    (innerRadius outerRadius broadening : ℝ) :
    lorentzianSpectralTailMass innerRadius outerRadius broadening =
      2 * (Real.arctan (outerRadius / broadening) -
        Real.arctan (innerRadius / broadening)) := by
  rw [lorentzianSpectralTailMass,
    integral_lorentzianSpectralKernel_symmetric,
    integral_lorentzianSpectralKernel_symmetric]
  ring

/-- The outer symmetric mass is the inner mass plus the spectral tail mass. -/
theorem integral_lorentzianSpectralKernel_outer_eq_inner_add_tail
    (innerRadius outerRadius broadening : ℝ) :
    (∫ offset in -outerRadius..outerRadius,
        lorentzianSpectralKernel offset broadening) =
      (∫ offset in -innerRadius..innerRadius,
        lorentzianSpectralKernel offset broadening) +
        lorentzianSpectralTailMass innerRadius outerRadius broadening := by
  unfold lorentzianSpectralTailMass
  ring

/-- For fixed positive nested radii, all Lorentzian mass between the two windows vanishes as the
broadening tends to zero from the positive side. -/
theorem tendsto_lorentzianSpectralTailMass_zero
    (innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius) (hnested : innerRadius ≤ outerRadius) :
    Tendsto
      (fun broadening : ℝ =>
        lorentzianSpectralTailMass innerRadius outerRadius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have houter : 0 < outerRadius := lt_of_lt_of_le hinner hnested
  have hOuterMass :=
    tendsto_integral_lorentzianSpectralKernel_symmetric outerRadius houter
  have hInnerMass :=
    tendsto_integral_lorentzianSpectralKernel_symmetric innerRadius hinner
  have htail := hOuterMass.sub hInnerMass
  simpa [lorentzianSpectralTailMass] using htail

end

end Transport
end QuantumTheory

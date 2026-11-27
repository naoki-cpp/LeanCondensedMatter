import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FunProp

set_option linter.style.header false

/-!
# Scalar Lorentzian kernels and integrals

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

/-- Elementary retarded-minus-advanced scalar resolvent identity. -/
theorem inv_add_I_sub_inv_sub_I_eq_spectralKernel
    (offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ((offset : ℂ) + (broadening : ℂ) * Complex.I)⁻¹ -
        ((offset : ℂ) - (broadening : ℂ) * Complex.I)⁻¹ =
      (-2 * Complex.I) * (spectralKernel offset broadening : ℂ) := by
  have hplus := complex_offset_add_I_ne_zero offset broadening hbroadening
  have hminus : (offset : ℂ) - (broadening : ℂ) * Complex.I ≠ 0 := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      (complex_offset_add_I_ne_zero offset (-broadening) (neg_ne_zero.mpr hbroadening))
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

/-- Negative distances give the negative half-mass arctangent limit. -/
theorem tendsto_arctan_neg_div_broadening
    (distance : ℝ) (hdistance : distance < 0) :
    Tendsto
      (fun broadening : ℝ => Real.arctan (distance / broadening))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-Real.pi / 2)) := by
  simpa only [neg_div, Real.arctan_neg, neg_neg] using
    (tendsto_arctan_pos_div_broadening (-distance) (neg_pos.mpr hdistance)).neg

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

/-- For any two fixed positive radii, the difference of their Lorentzian
symmetric-window masses tends to zero as broadening approaches zero
from the positive side. No nesting condition on the radii is needed. -/
theorem tendsto_spectralTailMass_zero
    (innerRadius outerRadius : ℝ)
    (hinner : 0 < innerRadius) (houter : 0 < outerRadius) :
    Tendsto
      (fun broadening : ℝ =>
        spectralTailMass innerRadius outerRadius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hOuterMass :=
    tendsto_integral_spectralKernel_symmetric outerRadius houter
  have hInnerMass :=
    tendsto_integral_spectralKernel_symmetric innerRadius hinner
  have htail := hOuterMass.sub hInnerMass
  simpa [spectralTailMass] using htail

end

end Lorentzian

/-!
# Weighted Lorentzian windows

This module owns representation-independent facts for multiplying the scalar Lorentzian kernel by a
weight that agrees almost everywhere with a constant on a centered finite window. Such a weight
factors out exactly, and therefore inherits the `π` symmetric-window mass in the positive
zero-broadening limit.

No occupation convention, Hamiltonian, band structure, current operator, or transport observable
appears here.
-/

namespace Lorentzian

noncomputable section

open Filter MeasureTheory

/-- If a weight is almost everywhere constant on the centered integration window, it factors out
exactly and the remaining energy integral is the centered Lorentzian mass. -/
theorem integral_weight_mul_spectralKernel_of_ae_eq_const_on
    (weight : ℝ → ℝ) (center value radius broadening : ℝ)
    (hweight : ∀ᵐ energy ∂(volume : Measure ℝ),
      energy ∈ Set.uIcc (center - radius) (center + radius) → weight energy = value) :
    (∫ energy in center - radius..center + radius,
        weight energy * spectralKernel (energy - center) broadening) =
      value * (∫ offset in -radius..radius,
        spectralKernel offset broadening) := by
  calc
    (∫ energy in center - radius..center + radius,
        weight energy * spectralKernel (energy - center) broadening) =
        ∫ energy in center - radius..center + radius,
          value * spectralKernel (energy - center) broadening := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hweight] with energy hweight henergy
      rw [hweight (Set.uIoc_subset_uIcc henergy)]
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

/-- Almost-everywhere constant weights inherit the `π` Lorentzian mass in the positive
zero-broadening limit. -/
theorem tendsto_integral_weight_mul_spectralKernel_of_ae_eq_const_on
    (weight : ℝ → ℝ) (center value radius : ℝ) (hradius : 0 < radius)
    (hweight : ∀ᵐ energy ∂(volume : Measure ℝ),
      energy ∈ Set.uIcc (center - radius) (center + radius) → weight energy = value) :
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
  exact (integral_weight_mul_spectralKernel_of_ae_eq_const_on
    weight center value radius broadening hweight).symm

end

end Lorentzian

/-!
## Radial quadratic Lorentzian calculus

These theorems belong to real analysis rather than to the transport namespace. They evaluate
model-independent radial integrals of the form

```text
∫ p dp / ((A - v² p²)² + B²).
```

For nonzero radial scale `v` and nonzero width `B`, Mathlib's substitution formula and
arctangent integral evaluate the finite-interval integral. For positive width, the same result
gives the convergent `pMax → +∞` limit and the scaled one-sided zero-width crossing limit. No Hamiltonian, disorder model, current vertex,
or transport normalization appears here.
-/

namespace Real

noncomputable section

open Filter MeasureTheory
open scoped Interval

/-- Exact finite-interval value of the radial quadratic Lorentzian integral. This is a
quadratic change of variables followed by Mathlib's integral of `(B² + u²)⁻¹`. -/
theorem integral_radialQuadraticLorentzian_eq_arctan
    (v A B pMax : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    (∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) =
      (2 * v ^ 2 * B)⁻¹ *
        (Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B) + Real.arctan (A / B)) := by
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hvelocity
  have hden (u : ℝ) : B ^ 2 + u ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hB, sq_nonneg u]
  have hderiv (p : ℝ) :
      HasDerivAt (fun q : ℝ => v ^ 2 * q ^ 2 - A) (2 * v ^ 2 * p) p := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).sub_const A)
  have hg : Continuous (fun u : ℝ => (B ^ 2 + u ^ 2)⁻¹) :=
    ((continuous_const.add (continuous_id.pow 2))).inv₀ hden
  have hsub :
      (∫ p in (0 : ℝ)..pMax,
        (B ^ 2 + (v ^ 2 * p ^ 2 - A) ^ 2)⁻¹ * (2 * v ^ 2 * p)) =
      ∫ u in -A..(v ^ 2 * pMax ^ 2 - A), (B ^ 2 + u ^ 2)⁻¹ := by
    simpa using
      (intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := pMax)
        (f := fun p : ℝ => v ^ 2 * p ^ 2 - A)
        (f' := fun p : ℝ => 2 * v ^ 2 * p)
        (g := fun u : ℝ => (B ^ 2 + u ^ 2)⁻¹)
        (fun p _ => hderiv p) (by fun_prop) hg)
  calc
    (∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) =
        (2 * v ^ 2)⁻¹ *
          (∫ p in (0 : ℝ)..pMax,
            (B ^ 2 + (v ^ 2 * p ^ 2 - A) ^ 2)⁻¹ * (2 * v ^ 2 * p)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro p _
      change p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) =
        (2 * v ^ 2)⁻¹ * ((B ^ 2 + (v ^ 2 * p ^ 2 - A) ^ 2)⁻¹ * (2 * v ^ 2 * p))
      rw [show (A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2 =
        B ^ 2 + (v ^ 2 * p ^ 2 - A) ^ 2 by ring]
      field_simp [hv2, hden (v ^ 2 * p ^ 2 - A)]
    _ = (2 * v ^ 2)⁻¹ *
          (∫ u in -A..(v ^ 2 * pMax ^ 2 - A), (B ^ 2 + u ^ 2)⁻¹) := by
      rw [hsub]
    _ = (2 * v ^ 2 * B)⁻¹ *
          (Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B) + Real.arctan (A / B)) := by
      rw [integral_inv_sq_add_sq hB]
      rw [show (-A) / B = -(A / B) by ring, Real.arctan_neg]
      field_simp [hv2, hB]
      ring

/-- If two continuously moving endpoints approach opposite sides of a resonance while a common
positive width tends to zero, their arctangent phase difference tends to `π`. -/
theorem tendsto_arctan_div_sub_arctan_div_nhdsGT_zero
    {ι : Type*} {l : Filter ι} {f g width : ι → ℝ} {a b : ℝ}
    (hf : Tendsto f l (nhds a)) (ha : 0 < a)
    (hg : Tendsto g l (nhds b)) (hb : b < 0)
    (hwidth : Tendsto width l (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun x => Real.arctan (f x / width x) - Real.arctan (g x / width x))
      l (nhds Real.pi) := by
  have hpos :
      Tendsto (fun x => Real.arctan (f x / width x)) l (nhds (Real.pi / 2)) := by
    change Tendsto (Real.arctan ∘ fun x => f x / width x) l (nhds (Real.pi / 2))
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp
          (hf.pos_mul_atTop ha (tendsto_inv_nhdsGT_zero.comp hwidth)))
  have hneg :
      Tendsto (fun x => Real.arctan (g x / width x)) l (nhds (-(Real.pi / 2))) := by
    change Tendsto (Real.arctan ∘ fun x => g x / width x) l (nhds (-(Real.pi / 2)))
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atBot.comp
          (hg.neg_mul_atTop hb (tendsto_inv_nhdsGT_zero.comp hwidth)))
  simpa only [show Real.pi / 2 - (-(Real.pi / 2)) = Real.pi by ring] using hpos.sub hneg

/-- A quadratic Lorentzian whose center approaches a value inside the fixed radial
cutoff has a finite scaled zero-width limit once its external scale cancels
the `1 / B` singularity. The outer-endpoint limit follows from center convergence. -/
theorem tendsto_scaled_integral_radialQuadraticLorentzian_nhdsGT_zero
    {ι : Type*} {l : Filter ι}
    (v pMax : ℝ) {center width scale : ι → ℝ} {a scaleLimit : ℝ}
    (hvelocity : v ≠ 0)
    (hcenter0 : Tendsto center l (nhds a)) (ha : 0 < a)
    (hcross : a - v ^ 2 * pMax ^ 2 < 0)
    (hwidth : Tendsto width l (nhdsWithin 0 (Set.Ioi 0)))
    (hscale : Tendsto (fun x => scale x * (2 * v ^ 2 * width x)⁻¹) l
      (nhds scaleLimit)) :
    Tendsto
      (fun x => scale x *
        ∫ p in (0 : ℝ)..pMax,
          p / ((center x - v ^ 2 * p ^ 2) ^ 2 + width x ^ 2))
      l (nhds (scaleLimit * Real.pi)) := by
  have hcenterMax :
      Tendsto (fun x => center x - v ^ 2 * pMax ^ 2) l
        (nhds (a - v ^ 2 * pMax ^ 2)) :=
    hcenter0.sub tendsto_const_nhds
  have hphase := tendsto_arctan_div_sub_arctan_div_nhdsGT_zero
    hcenter0 ha hcenterMax hcross hwidth
  apply Tendsto.congr' ?_ (hscale.mul hphase)
  filter_upwards [hwidth.eventually self_mem_nhdsWithin] with x hwidthPos
  rw [integral_radialQuadraticLorentzian_eq_arctan
    v (center x) (width x) pMax hvelocity (ne_of_gt hwidthPos)]
  rw [show
      (v ^ 2 * pMax ^ 2 - center x) / width x =
        -((center x - v ^ 2 * pMax ^ 2) / width x) by ring,
    Real.arctan_neg]
  ring

/-- For nonzero radial scale and positive width, the radial quadratic Lorentzian integral converges
as the upper cutoff tends to `+∞`. -/
theorem tendsto_integral_radialQuadraticLorentzian_atTop
    (v A B : ℝ) (hvelocity : v ≠ 0) (hB : 0 < B) :
    Tendsto
      (fun pMax : ℝ =>
        ∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2))
      atTop
      (nhds
        ((2 * v ^ 2 * B)⁻¹ *
          (Real.pi / 2 + Real.arctan (A / B)))) := by
  have harg : Tendsto (fun p : ℝ => (v ^ 2 * p ^ 2 - A) / B) atTop atTop := by
    have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hvelocity
    have hp2 : Tendsto (fun p : ℝ => p ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    have hlead : Tendsto (fun p : ℝ => v ^ 2 * p ^ 2) atTop atTop :=
      hp2.const_mul_atTop hv2
    have hshift0 := tendsto_atTop_add_const_right atTop (-A) hlead
    have hshift : Tendsto (fun p : ℝ => v ^ 2 * p ^ 2 - A) atTop atTop := by
      simpa [sub_eq_add_neg] using hshift0
    exact hshift.atTop_div_const hB
  have harctan :
      Tendsto
        (fun pMax : ℝ => Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B))
        atTop (nhds (Real.pi / 2)) := by
    simpa [Function.comp_def] using
      (Real.tendsto_arctan_atTop.comp harg).mono_right inf_le_left
  have hsum := harctan.add
    (tendsto_const_nhds : Tendsto (fun _pMax : ℝ => Real.arctan (A / B))
      atTop (nhds (Real.arctan (A / B))))
  refine ((tendsto_const_nhds : Tendsto (fun _pMax : ℝ => (2 * v ^ 2 * B)⁻¹)
    atTop (nhds ((2 * v ^ 2 * B)⁻¹))).mul hsum).congr' ?_
  exact Eventually.of_forall fun pMax =>
    (integral_radialQuadraticLorentzian_eq_arctan
      v A B pMax hvelocity (ne_of_gt hB)).symm

end

end Real

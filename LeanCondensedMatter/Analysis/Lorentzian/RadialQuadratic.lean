import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial quadratic Lorentzian calculus

These theorems belong to real analysis rather than to the transport namespace. They evaluate
model-independent radial integrals of the form

```text
∫ p dp / ((A - v² p²)² + B²).
```

For nonzero radial scale `v` and nonzero width `B`, the finite-interval integral is evaluated by an
arctangent primitive. For positive width, the same formula gives the convergent `pMax → +∞` limit
and the scaled one-sided zero-width crossing limit. No Hamiltonian, disorder model, current vertex,
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
    convert ((((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).sub_const A) using 1 <;> ring
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
      ring
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

/-- A moving quadratic Lorentzian whose endpoints approach opposite sides of the resonance has a
finite scaled zero-width limit once its external scale cancels the `1 / B` singularity. -/
theorem tendsto_scaled_integral_radialQuadraticLorentzian_nhdsGT_zero
    {ι : Type*} {l : Filter ι}
    (v pMax : ℝ) {center width scale : ι → ℝ} {a b scaleLimit : ℝ}
    (hvelocity : v ≠ 0)
    (hcenter0 : Tendsto center l (nhds a)) (ha : 0 < a)
    (hcenterMax : Tendsto (fun x => center x - v ^ 2 * pMax ^ 2) l (nhds b))
    (hb : b < 0)
    (hwidth : Tendsto width l (nhdsWithin 0 (Set.Ioi 0)))
    (hscale : Tendsto (fun x => scale x * (2 * v ^ 2 * width x)⁻¹) l
      (nhds scaleLimit)) :
    Tendsto
      (fun x => scale x *
        ∫ p in (0 : ℝ)..pMax,
          p / ((center x - v ^ 2 * p ^ 2) ^ 2 + width x ^ 2))
      l (nhds (scaleLimit * Real.pi)) := by
  have hphase := tendsto_arctan_div_sub_arctan_div_nhdsGT_zero
    hcenter0 ha hcenterMax hb hwidth
  apply Tendsto.congr' ?_ (hscale.mul hphase)
  filter_upwards [hwidth.eventually self_mem_nhdsWithin] with x hwidthPos
  rw [integral_radialQuadraticLorentzian_eq_arctan
    v (center x) (width x) pMax hvelocity (ne_of_gt hwidthPos)]
  rw [show
      (v ^ 2 * pMax ^ 2 - center x) / width x =
        -((center x - v ^ 2 * pMax ^ 2) / width x) by ring,
    Real.arctan_neg]
  ring

private theorem tendsto_radialQuadraticLorentzianArctanArgument_atTop
    (v A B : ℝ) (hvelocity : v ≠ 0) (hB : 0 < B) :
    Tendsto (fun p : ℝ => (v ^ 2 * p ^ 2 - A) / B) atTop atTop := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hvelocity
  have hp2 : Tendsto (fun p : ℝ => p ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hlead : Tendsto (fun p : ℝ => v ^ 2 * p ^ 2) atTop atTop :=
    hp2.const_mul_atTop hv2
  have hshift0 := tendsto_atTop_add_const_right atTop (-A) hlead
  have hshift : Tendsto (fun p : ℝ => v ^ 2 * p ^ 2 - A) atTop atTop := by
    simpa [sub_eq_add_neg] using hshift0
  exact hshift.atTop_div_const hB

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
  have harctan :
      Tendsto
        (fun pMax : ℝ => Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B))
        atTop (nhds (Real.pi / 2)) := by
    simpa [Function.comp_def] using
      (Real.tendsto_arctan_atTop.comp
        (tendsto_radialQuadraticLorentzianArctanArgument_atTop
          v A B hvelocity hB)).mono_right inf_le_left
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

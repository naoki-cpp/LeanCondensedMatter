import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial quadratic Lorentzian calculus

This module owns the model-independent real analysis for radial integrals of the form

```text
∫ p dp / ((A - v² p²)² + B²).
```

For nonzero radial scale `v` and nonzero width `B`, the finite-interval integral is evaluated by an
arctangent primitive.  For positive width, the same formula gives the convergent `pMax → +∞`
limit.  No Hamiltonian, disorder model, current vertex, or transport normalization appears here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open Filter MeasureTheory
open scoped Interval

private def radialQuadraticLorentzianPrimitive (v A B p : ℝ) : ℝ :=
  (2 * v ^ 2 * B)⁻¹ * Real.arctan ((v ^ 2 * p ^ 2 - A) / B)

private theorem radialQuadraticLorentzianDenominator_ne_zero
    (v A B p : ℝ) (hB : B ≠ 0) :
    (A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2 ≠ 0 := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  nlinarith [sq_nonneg (A - v ^ 2 * p ^ 2)]

private theorem continuous_radialQuadraticLorentzianIntegrand
    (v A B : ℝ) (hB : B ≠ 0) :
    Continuous (fun p : ℝ => p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) := by
  have hden : Continuous (fun p : ℝ => (A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) := by
    fun_prop
  exact continuous_id.div hden
    (fun p => radialQuadraticLorentzianDenominator_ne_zero v A B p hB)

private theorem hasDerivAt_radialQuadraticLorentzianPrimitive
    (v A B p : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    HasDerivAt (radialQuadraticLorentzianPrimitive v A B)
      (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) p := by
  have hu :
      HasDerivAt (fun q : ℝ => (v ^ 2 * q ^ 2 - A) / B)
        ((2 * v ^ 2 * p) / B) p := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).sub_const A).div_const B
  have hmain := hu.arctan.const_mul ((2 * v ^ 2 * B)⁻¹)
  unfold radialQuadraticLorentzianPrimitive
  convert hmain using 1 <;> try rfl
  field_simp [hvelocity, hB]
  ring

private theorem integral_radialQuadraticLorentzian_eq_primitive_sub
    (v A B pMax : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    (∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) =
      radialQuadraticLorentzianPrimitive v A B pMax -
        radialQuadraticLorentzianPrimitive v A B 0 := by
  have hint : IntervalIntegrable
      (fun p : ℝ => p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2))
      volume 0 pMax :=
    (continuous_radialQuadraticLorentzianIntegrand v A B hB).intervalIntegrable 0 pMax
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hasDerivAt_radialQuadraticLorentzianPrimitive v A B p hvelocity hB) hint

/-- Exact finite-interval value of the radial quadratic Lorentzian integral. -/
theorem integral_radialQuadraticLorentzian_eq_arctan
    (v A B pMax : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    (∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) =
      (2 * v ^ 2 * B)⁻¹ *
        (Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B) + Real.arctan (A / B)) := by
  rw [integral_radialQuadraticLorentzian_eq_primitive_sub v A B pMax hvelocity hB]
  unfold radialQuadraticLorentzianPrimitive
  have hzero : (v ^ 2 * (0 : ℝ) ^ 2 - A) / B = -(A / B) := by
    ring
  rw [hzero, Real.arctan_neg]
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

end Transport
end QuantumTheory

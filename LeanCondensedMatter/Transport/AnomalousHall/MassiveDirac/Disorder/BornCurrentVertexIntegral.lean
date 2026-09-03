import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexRadial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial evaluation of the Born retarded-advanced current rung

This Phase 5 slice evaluates the real radial denominator integral left by
`BornCurrentVertexRadial.lean`.  At fixed Born damping the common radial kernel is

```text
p / ((A - v² p²)² + B²),
```

with

```text
A = (1 - γ²) (ε² - m²),
B = 2 γ (ε² + m²).
```

The finite-cutoff integral is evaluated exactly by an arctangent primitive.  For positive width
`B`, the radial cutoff is then removed in a separate `pMax → +∞` theorem.  This convergent radial
limit is kept distinct from the later weak-disorder limit `γ → 0⁺`.

No ladder fixed point, transport-lifetime identification, Kubo–Středa insertion, Ward claim, or
conductivity theorem is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory
open QuantumTheory.Transport
open scoped Interval

private def radialLorentzianPrimitive (v A B p : ℝ) : ℝ :=
  (2 * v ^ 2 * B)⁻¹ * Real.arctan ((v ^ 2 * p ^ 2 - A) / B)

private theorem radialLorentzianDenominator_ne_zero
    (v A B p : ℝ) (hB : B ≠ 0) :
    (A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2 ≠ 0 := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  nlinarith [sq_nonneg (A - v ^ 2 * p ^ 2)]

private theorem continuous_radialLorentzianIntegrand
    (v A B : ℝ) (hB : B ≠ 0) :
    Continuous (fun p : ℝ => p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) := by
  have hden : Continuous (fun p : ℝ => (A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) := by
    fun_prop
  exact continuous_id.div hden (fun p => radialLorentzianDenominator_ne_zero v A B p hB)

private theorem hasDerivAt_radialLorentzianPrimitive
    (v A B p : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    HasDerivAt (radialLorentzianPrimitive v A B)
      (p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) p := by
  have hu :
      HasDerivAt (fun q : ℝ => (v ^ 2 * q ^ 2 - A) / B)
        ((2 * v ^ 2 * p) / B) p := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).sub_const A).div_const B
  have hmain := hu.arctan.const_mul ((2 * v ^ 2 * B)⁻¹)
  unfold radialLorentzianPrimitive
  convert hmain using 1 <;> try rfl
  field_simp [hvelocity, hB]
  ring

private theorem integral_radialLorentzian_eq_primitive_sub
    (v A B pMax : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    (∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) =
      radialLorentzianPrimitive v A B pMax - radialLorentzianPrimitive v A B 0 := by
  have hint : IntervalIntegrable
      (fun p : ℝ => p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2))
      volume 0 pMax :=
    (continuous_radialLorentzianIntegrand v A B hB).intervalIntegrable 0 pMax
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun p _ => hasDerivAt_radialLorentzianPrimitive v A B p hvelocity hB) hint

private theorem integral_radialLorentzian_eq_arctan
    (v A B pMax : ℝ) (hvelocity : v ≠ 0) (hB : B ≠ 0) :
    (∫ p in (0 : ℝ)..pMax, p / ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) =
      (2 * v ^ 2 * B)⁻¹ *
        (Real.arctan ((v ^ 2 * pMax ^ 2 - A) / B) + Real.arctan (A / B)) := by
  rw [integral_radialLorentzian_eq_primitive_sub v A B pMax hvelocity hB]
  unfold radialLorentzianPrimitive
  have hzero : (v ^ 2 * (0 : ℝ) ^ 2 - A) / B = -(A / B) := by
    ring
  rw [hzero, Real.arctan_neg]
  ring

/-- Finite-cutoff real radial denominator integral shared by the Born `σₓ` and `σᵧ` current-rung
channels.  This contains the `p dp` Jacobian but no numerator or continuum prefactor. -/
noncomputable def finiteCutoffContinuumBornRARadialIntegral
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  ∫ p in (0 : ℝ)..pMax,
    p / continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar

/-- Exact finite-cutoff arctangent evaluation of the shared Born RA radial denominator integral. -/
theorem finiteCutoffContinuumBornRARadialIntegral_eq_arctan
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0)
    (hwidth : continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar ≠ 0) :
    finiteCutoffContinuumBornRARadialIntegral
        v m probeEnergy disorderStrength hbar pMax =
      (2 * v ^ 2 *
          continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)⁻¹ *
        (Real.arctan
            ((v ^ 2 * pMax ^ 2 -
                (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
                  (probeEnergy ^ 2 - m ^ 2)) /
              continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar) +
          Real.arctan
            (((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
                (probeEnergy ^ 2 - m ^ 2)) /
              continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)) := by
  unfold finiteCutoffContinuumBornRARadialIntegral
  simpa [continuumBornRADenominatorProduct, continuumBornRADenominatorCenter] using
    integral_radialLorentzian_eq_arctan
      v
      ((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))
      (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
      pMax hvelocity hwidth

private theorem tendsto_radialLorentzianArctanArgument_atTop
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

private theorem tendsto_integral_radialLorentzian_atTop
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
        (tendsto_radialLorentzianArctanArgument_atTop v A B hvelocity hB)).mono_right
          inf_le_left
  have hsum := harctan.add
    (tendsto_const_nhds : Tendsto (fun _pMax : ℝ => Real.arctan (A / B))
      atTop (nhds (Real.arctan (A / B))))
  refine ((tendsto_const_nhds : Tendsto (fun _pMax : ℝ => (2 * v ^ 2 * B)⁻¹)
    atTop (nhds ((2 * v ^ 2 * B)⁻¹))).mul hsum).congr' ?_
  exact Eventually.of_forall fun pMax =>
    (integral_radialLorentzian_eq_arctan
      v A B pMax hvelocity (ne_of_gt hB)).symm

/-- Infinite-cutoff value of the convergent Born RA radial denominator integral at positive width.
This is an analytic target for the separate `pMax → +∞` theorem, not a definition of the finite
integral. -/
def continuumBornRARadialIntegralUVLimit
    (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (2 * v ^ 2 *
      continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)⁻¹ *
    (Real.pi / 2 +
      Real.arctan
        (((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2)) /
          continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar))

/-- For nonzero velocity and positive Born RA width, the finite radial integral converges as the
cutoff tends to `+∞` to its explicit arctangent value. -/
theorem tendsto_finiteCutoffContinuumBornRARadialIntegral_atTop
    (v m probeEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0)
    (hwidth : 0 < continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar) :
    Tendsto
      (fun pMax : ℝ =>
        finiteCutoffContinuumBornRARadialIntegral
          v m probeEnergy disorderStrength hbar pMax)
      atTop
      (nhds (continuumBornRARadialIntegralUVLimit
        v m probeEnergy disorderStrength hbar)) := by
  unfold finiteCutoffContinuumBornRARadialIntegral continuumBornRARadialIntegralUVLimit
  simpa [continuumBornRADenominatorProduct, continuumBornRADenominatorCenter] using
    tendsto_integral_radialLorentzian_atTop
      v
      ((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))
      (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
      hvelocity hwidth

end

end AnomalousHall.MassiveDirac

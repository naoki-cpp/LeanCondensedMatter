import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexRung
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Infinite-cutoff Born retarded-advanced current rung

This module uses the model-independent radial quadratic Lorentzian calculus to take the
`pMax → +∞` Born current-rung limit. The shared real radial denominator integral is evaluated
exactly by an arctangent formula, then used for the direction-indexed in-plane output coefficient.

The continuum disorder is parameterized by `W(γ) = 4 γ ℏ² v²`. In the metallic regime
`m² < ε²`, the `.x` infinite-cutoff coefficient tends to the canonical weak-disorder rung
coefficient, while in repository orientation `Gᴿ σₓ Gᴬ`

```text
Y₁ / γ → 2 ε m / (ε² + m²).
```

The convergent radial cutoff limit is kept distinct from the later `γ → 0⁺` limit. This module does
not solve a new ladder equation, insert the result into Kubo–Středa, claim Ward consistency, or
include crossed diagrams.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Finite-cutoff real radial denominator integral shared by both in-plane current-rung outputs.
This contains the `p dp` Jacobian but no numerator or continuum prefactor. -/
private noncomputable def finiteCutoffContinuumBornRARadialIntegral
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  ∫ p in (0 : ℝ)..pMax,
    p / continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar

/-- Exact finite-cutoff arctangent evaluation of the shared Born RA radial denominator integral. -/
private theorem finiteCutoffContinuumBornRARadialIntegral_eq_arctan
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
    integral_radialQuadraticLorentzian_eq_arctan
      v
      ((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))
      (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
      pMax hvelocity hwidth

/-- Infinite-cutoff value of the convergent Born RA radial denominator integral at positive width. -/
private def continuumBornRARadialIntegralUVLimit
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
private theorem tendsto_finiteCutoffContinuumBornRARadialIntegral_atTop
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
    tendsto_integral_radialQuadraticLorentzian_atTop
      v
      ((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))
      (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
      hvelocity hwidth

/-- Each normalized finite-cutoff in-plane output coefficient factors through the same real radial
denominator integral. -/
private theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_eq_radialIntegral
    (output : Direction2) (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient output
        v m probeEnergy disorderStrength hbar pMax =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
        continuumBornRetardedAdvancedPauliXAngularNumerator output
          v m probeEnergy disorderStrength hbar) *
        finiteCutoffContinuumBornRARadialIntegral
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient
    continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal
    finiteCutoffContinuumBornRARadialIntegral
  rw [show
      (fun p : ℝ =>
        continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar * p *
          continuumBornRetardedAdvancedPauliXAngularNumerator output
            v m probeEnergy disorderStrength hbar *
          (continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar)⁻¹) =
      (fun p : ℝ =>
        (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          continuumBornRetardedAdvancedPauliXAngularNumerator output
            v m probeEnergy disorderStrength hbar) *
          (p / continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar)) by
    funext p
    rw [div_eq_mul_inv]
    ring]
  rw [intervalIntegral.integral_const_mul]

/-- Infinite-cutoff full one-rung coefficient in the selected in-plane output direction. -/
def continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV
    (output : Direction2) (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    continuumBornRetardedAdvancedPauliXAngularNumerator output
      v m probeEnergy disorderStrength hbar) *
    continuumBornRARadialIntegralUVLimit v m probeEnergy disorderStrength hbar

/-- At fixed positive Born width, every in-plane output coefficient converges to its indexed
infinite-cutoff value. -/
theorem tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_atTop
    (output : Direction2) (v m probeEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0)
    (hwidth : 0 < continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar) :
    Tendsto
      (fun pMax : ℝ =>
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient output
          v m probeEnergy disorderStrength hbar pMax)
      atTop
      (nhds (continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV output
        v m probeEnergy disorderStrength hbar)) := by
  have hradial := tendsto_finiteCutoffContinuumBornRARadialIntegral_atTop
    v m probeEnergy disorderStrength hbar hvelocity hwidth
  simpa [continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV] using
    (tendsto_const_nhds.mul hradial).congr' (Eventually.of_forall fun pMax =>
      (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_eq_radialIntegral
        output v m probeEnergy disorderStrength hbar pMax).symm)

/-- Continuum disorder strength corresponding exactly to a chosen Born damping scale `γ`. -/
def continuumBornWeakDisorderStrength (v hbar gamma : ℝ) : ℝ :=
  4 * gamma * hbar ^ 2 * v ^ 2

/-- The weak-disorder parameterization `W(γ) = 4 γ ℏ² v²` exactly inverts the Born damping scale. -/
theorem continuumBornDampingScale_weakDisorderStrength
    (v hbar gamma : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornDampingScale v (continuumBornWeakDisorderStrength v hbar gamma) hbar = gamma := by
  unfold continuumBornDampingScale continuumBornWeakDisorderStrength
  field_simp [hvelocity, hhbar]

/-- Under `W(γ) = 4 γ ℏ² v²`, the RA denominator width is `2γ(ε²+m²)`. -/
theorem continuumBornRADenominatorWidth_weakDisorderStrength
    (v m probeEnergy hbar gamma : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornRADenominatorWidth v m probeEnergy
        (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      2 * gamma * (probeEnergy ^ 2 + m ^ 2) := by
  unfold continuumBornRADenominatorWidth
  rw [continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar]

/-- Under the weak-disorder parameterization the physical current-rung prefactor is
`γ v² / π²`. -/
theorem continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength
    (v hbar gamma : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornRetardedAdvancedCurrentRungPrefactor
        (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      gamma * v ^ 2 / Real.pi ^ 2 := by
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_eq_dampingScale
    v (continuumBornWeakDisorderStrength v hbar gamma) hbar hvelocity hhbar]
  rw [continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar]

/-- Arctangent mass controlling the infinite-cutoff metallic weak-disorder limit. -/
private def continuumBornRAWeakDisorderArctanMass
    (m probeEnergy gamma : ℝ) : ℝ :=
  Real.pi / 2 +
    Real.arctan
      (((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
        (2 * gamma * (probeEnergy ^ 2 + m ^ 2)))

/-- Exact infinite-cutoff longitudinal coefficient under the weak-disorder parameterization. -/
private theorem continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_x_weakDisorderStrength_eq
    (v m probeEnergy hbar gamma : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hgamma : gamma ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV .x
        v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      ((1 + gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2) /
        (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        continuumBornRAWeakDisorderArctanMass m probeEnergy gamma := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV
    continuumBornRetardedAdvancedPauliXAngularNumerator
    continuumBornRARadialIntegralUVLimit continuumBornRAWeakDisorderArctanMass
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength
      v hbar gamma hvelocity hhbar,
    continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar,
    continuumBornRADenominatorWidth_weakDisorderStrength
      v m probeEnergy hbar gamma hvelocity hhbar]
  field_simp [hvelocity, hhbar, hgamma, ne_of_gt hsum, Real.pi_ne_zero]

/-- Exact infinite-cutoff transverse coefficient in repository orientation `Gᴿ σₓ Gᴬ` under the
weak-disorder parameterization. -/
private theorem continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_y_weakDisorderStrength_eq
    (v m probeEnergy hbar gamma : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hgamma : gamma ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV .y
        v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      (2 * gamma * probeEnergy * m /
        (Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        continuumBornRAWeakDisorderArctanMass m probeEnergy gamma := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV
    continuumBornRetardedAdvancedPauliXAngularNumerator
    continuumBornRARadialIntegralUVLimit continuumBornRAWeakDisorderArctanMass
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength
      v hbar gamma hvelocity hhbar,
    continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar,
    continuumBornRADenominatorWidth_weakDisorderStrength
      v m probeEnergy hbar gamma hvelocity hhbar]
  (field_simp [hvelocity, hhbar, hgamma, ne_of_gt hsum, Real.pi_ne_zero]; ring)

/-- In the metallic regime the infinite-cutoff arctangent mass tends to `π` as `γ → 0⁺`. -/
private theorem tendsto_continuumBornRAWeakDisorderArctanMass_zero
    (m probeEnergy : ℝ) (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (continuumBornRAWeakDisorderArctanMass m probeEnergy)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  let distance : ℝ := (probeEnergy ^ 2 - m ^ 2) /
    (2 * (probeEnergy ^ 2 + m ^ 2))
  have hdistance : 0 < distance := by
    dsimp [distance]
    exact div_pos (sub_pos.mpr hmetal) (mul_pos (by norm_num) hsum)
  have hlarge : Tendsto (fun gamma : ℝ => distance * gamma⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => distance)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds distance)).pos_mul_atTop hdistance
      tendsto_inv_nhdsGT_zero
  have hgamma0 : Tendsto (fun gamma : ℝ => gamma)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact tendsto_id.mono_left inf_le_left
  have hsmall : Tendsto (fun gamma : ℝ => -(distance * gamma))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => distance)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds distance)).mul hgamma0).neg
  have harg : Tendsto
      (fun gamma : ℝ =>
        ((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
          (2 * gamma * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    refine (Tendsto.atTop_add hlarge hsmall).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with gamma hgamma
    have hgamma_pos : 0 < gamma := by
      simpa only [Set.mem_Ioi] using hgamma
    dsimp [distance]
    (field_simp [ne_of_gt hgamma_pos, ne_of_gt hsum]; ring)
  have harctan : Tendsto
      (fun gamma : ℝ =>
        Real.arctan
          (((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
            (2 * gamma * (probeEnergy ^ 2 + m ^ 2))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    simpa [Function.comp_def] using
      tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp harg)
  have hhalf : Tendsto (fun _gamma : ℝ => Real.pi / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := tendsto_const_nhds
  change Tendsto
    (fun gamma : ℝ =>
      Real.pi / 2 +
        Real.arctan
          (((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
            (2 * gamma * (probeEnergy ^ 2 + m ^ 2))))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi)
  simpa only [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring] using hhalf.add harctan

private theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_x_weakDisorder_closed
    (v m probeEnergy hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (fun gamma : ℝ =>
        continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV .x
          v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((probeEnergy ^ 2 - m ^ 2) /
        (2 * (probeEnergy ^ 2 + m ^ 2)))) := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  have hgamma0 : Tendsto (fun gamma : ℝ => gamma)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact tendsto_id.mono_left inf_le_left
  have hshape : Tendsto (fun gamma : ℝ => 1 + gamma ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using (tendsto_const_nhds.add (hgamma0.pow 2))
  have hfactor : Tendsto
      (fun gamma : ℝ =>
        (1 + gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((probeEnergy ^ 2 - m ^ 2) /
        (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      hshape.mul (tendsto_const_nhds : Tendsto
        (fun _gamma : ℝ =>
          (probeEnergy ^ 2 - m ^ 2) /
            (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))))
  have hprod := hfactor.mul
    (tendsto_continuumBornRAWeakDisorderArctanMass_zero m probeEnergy hmetal)
  have htarget :
      ((probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) * Real.pi =
        (probeEnergy ^ 2 - m ^ 2) /
          (2 * (probeEnergy ^ 2 + m ^ 2)) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hsum]
  rw [htarget] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with gamma hgamma
  have hgamma_pos : 0 < gamma := by
    simpa only [Set.mem_Ioi] using hgamma
  exact (continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_x_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar (ne_of_gt hgamma_pos) hmetal).symm

/-- Metallic weak-disorder limit of the infinite-cutoff longitudinal one-rung coefficient. The
limit is the canonical scalar rung coefficient already used by the fixed-cutoff transport bridge. -/
theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_x_weakDisorder
    (v m probeEnergy hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (fun gamma : ℝ =>
        continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV .x
          v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy)) := by
  simpa [continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient] using
    tendsto_continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_x_weakDisorder_closed
      v m probeEnergy hbar hvelocity hhbar hmetal

/-- Exact scaled transverse coefficient under the weak-disorder parameterization. -/
private theorem continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_y_div_gamma_weakDisorderStrength_eq
    (v m probeEnergy hbar gamma : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hgamma : gamma ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV .y
        v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar / gamma =
      (2 * probeEnergy * m /
        (Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        continuumBornRAWeakDisorderArctanMass m probeEnergy gamma := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_y_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar hgamma hmetal]
  field_simp [hgamma]

/-- Metallic weak-disorder limit of the leading transverse one-rung coefficient. The unscaled
`.y` coefficient is `O(γ)`; the limit below exposes its positive repository-orientation coefficient. -/
theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_y_div_gamma_weakDisorder
    (v m probeEnergy hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (fun gamma : ℝ =>
        continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV .y
          v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar / gamma)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * probeEnergy * m / (probeEnergy ^ 2 + m ^ 2))) := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  have hprod :=
    (tendsto_const_nhds : Tendsto
      (fun _gamma : ℝ =>
        2 * probeEnergy * m /
          (Real.pi * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * probeEnergy * m /
        (Real.pi * (probeEnergy ^ 2 + m ^ 2))))).mul
      (tendsto_continuumBornRAWeakDisorderArctanMass_zero m probeEnergy hmetal)
  have htarget :
      (2 * probeEnergy * m /
          (Real.pi * (probeEnergy ^ 2 + m ^ 2))) * Real.pi =
        2 * probeEnergy * m / (probeEnergy ^ 2 + m ^ 2) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hsum]
  rw [htarget] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with gamma hgamma
  have hgamma_pos : 0 < gamma := by
    simpa only [Set.mem_Ioi] using hgamma
  exact (continuumBornRetardedAdvancedPauliXCurrentRungCoefficientUV_y_div_gamma_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar (ne_of_gt hgamma_pos) hmetal).symm

end

end QuantumTheory.Transport.Models.MassiveDirac

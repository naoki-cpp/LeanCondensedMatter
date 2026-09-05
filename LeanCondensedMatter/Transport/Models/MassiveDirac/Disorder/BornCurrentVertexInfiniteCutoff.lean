import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Infinite-cutoff Born retarded-advanced current rung

This module uses the model-independent radial quadratic Lorentzian calculus to take the
`pMax → +∞` Born current-rung limit.  The shared real radial denominator integral is evaluated
exactly by an arctangent formula, then used for both longitudinal and orientation-sensitive
transverse current-rung coefficients.

The continuum disorder is parameterized by `W(γ) = 4 γ ℏ² v²`.  In the metallic regime
`m² < ε²`, the infinite-cutoff longitudinal coefficient tends to the canonical weak-disorder rung
coefficient, while in repository orientation `Gᴿ σₓ Gᴬ`

```text
Y₁ / γ → 2 ε m / (ε² + m²).
```

The convergent radial cutoff limit is kept distinct from the later `γ → 0⁺` limit.  This module does
not solve a new ladder equation, insert the result into Kubo–Středa, claim Ward consistency, or
include crossed diagrams.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory
open QuantumTheory.Transport
open scoped Interval

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
    integral_radialQuadraticLorentzian_eq_arctan
      v
      ((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))
      (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
      pMax hvelocity hwidth

/-- Infinite-cutoff value of the convergent Born RA radial denominator integral at positive width. -/
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
    tendsto_integral_radialQuadraticLorentzian_atTop
      v
      ((1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))
      (continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar)
      hvelocity hwidth

/-- Real-valued closed form of the normalized radial `σᵧ` current-rung integrand in repository
orientation `Gᴿ σₓ Gᴬ`. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    8 * Real.pi * p * continuumBornDampingScale v disorderStrength hbar *
    probeEnergy * m *
    (continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar)⁻¹

/-- The real transverse current-rung kernel embeds exactly into the existing complex radial API. -/
theorem coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    (continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
        v m p probeEnergy disorderStrength hbar : ℂ) =
      continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
        v m p probeEnergy disorderStrength hbar := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq_closed]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
  push_cast
  ring

/-- Finite-cutoff real `σᵧ` coefficient of the fully normalized Born RA current rung. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
      v m p probeEnergy disorderStrength hbar

/-- The normalized finite-cutoff transverse coefficient is the integrated Green-product
`σᵧ` coefficient multiplied by the physical current-rung prefactor. -/
theorem coe_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient_eq_prefactor_mul_greenProduct
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
        finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
  rw [← Complex.ofRealLI_apply
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
        v m p probeEnergy disorderStrength hbar)]
  rw [← Complex.ofRealLI.intervalIntegral_comp_comm]
  rw [show
      (fun p : ℝ => Complex.ofRealLI
        (continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
          v m p probeEnergy disorderStrength hbar)) =
      (fun p : ℝ =>
        (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
          continuumBornRetardedAdvancedPauliXRadialYIntegrand
            v m p probeEnergy disorderStrength hbar) by
    funext p
    rw [Complex.ofRealLI_apply,
      coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal]
    rfl]
  rw [intervalIntegral.integral_const_mul]
  rfl

private theorem finiteCutoffContinuumBornCurrentRungCoefficient_eq_radialIntegral
    (v m probeEnergy disorderStrength hbar pMax prefactor : ℝ)
    (integrand : ℝ → ℝ)
    (hfactor : ∀ p,
      integrand p =
        prefactor * (p / continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar)) :
    (∫ p in (0 : ℝ)..pMax, integrand p) =
      prefactor * finiteCutoffContinuumBornRARadialIntegral
        v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRARadialIntegral
  simp_rw [hfactor]
  rw [intervalIntegral.integral_const_mul]

/-- The canonical finite-cutoff longitudinal coefficient factors through the shared real radial
integral. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_radialIntegral
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        v m probeEnergy disorderStrength hbar pMax =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
        (2 * Real.pi *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2))) *
        finiteCutoffContinuumBornRARadialIntegral
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
  apply finiteCutoffContinuumBornCurrentRungCoefficient_eq_radialIntegral
  intro p
  unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
  rw [div_eq_mul_inv]
  ring

/-- The finite-cutoff transverse coefficient factors through the same shared real radial integral. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient_eq_radialIntegral
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
        v m probeEnergy disorderStrength hbar pMax =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
        (8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m)) *
        finiteCutoffContinuumBornRARadialIntegral
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
  apply finiteCutoffContinuumBornCurrentRungCoefficient_eq_radialIntegral
  intro p
  unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrandReal
  rw [div_eq_mul_inv]
  ring

/-- Infinite-cutoff full `σₓ` one-rung coefficient at fixed positive Born width. -/
def continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV
    (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    (2 * Real.pi *
      (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2)) *
    continuumBornRARadialIntegralUVLimit
      v m probeEnergy disorderStrength hbar

/-- Infinite-cutoff full `σᵧ` one-rung coefficient in repository orientation `Gᴿ σₓ Gᴬ`. -/
def continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV
    (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    (8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
      probeEnergy * m) *
    continuumBornRARadialIntegralUVLimit
      v m probeEnergy disorderStrength hbar

/-- At fixed positive Born width, the canonical finite-cutoff longitudinal coefficient converges to
its infinite-cutoff value. -/
theorem tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_atTop
    (v m probeEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0)
    (hwidth : 0 < continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar) :
    Tendsto
      (fun pMax : ℝ =>
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
          v m probeEnergy disorderStrength hbar pMax)
      atTop
      (nhds (continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV
        v m probeEnergy disorderStrength hbar)) := by
  have hradial := tendsto_finiteCutoffContinuumBornRARadialIntegral_atTop
    v m probeEnergy disorderStrength hbar hvelocity hwidth
  simpa [continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV] using
    (tendsto_const_nhds.mul hradial).congr' (Eventually.of_forall fun pMax =>
      (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_radialIntegral
        v m probeEnergy disorderStrength hbar pMax).symm)

/-- At fixed positive Born width, the finite-cutoff transverse coefficient converges to its
infinite-cutoff value. -/
theorem tendsto_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient_atTop
    (v m probeEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0)
    (hwidth : 0 < continuumBornRADenominatorWidth
      v m probeEnergy disorderStrength hbar) :
    Tendsto
      (fun pMax : ℝ =>
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
          v m probeEnergy disorderStrength hbar pMax)
      atTop
      (nhds (continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV
        v m probeEnergy disorderStrength hbar)) := by
  have hradial := tendsto_finiteCutoffContinuumBornRARadialIntegral_atTop
    v m probeEnergy disorderStrength hbar hvelocity hwidth
  simpa [continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV] using
    (tendsto_const_nhds.mul hradial).congr' (Eventually.of_forall fun pMax =>
      (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient_eq_radialIntegral
        v m probeEnergy disorderStrength hbar pMax).symm)

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
theorem continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorderStrength_eq
    (v m probeEnergy hbar gamma : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hgamma : gamma ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV
        v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      ((1 + gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2) /
        (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        continuumBornRAWeakDisorderArctanMass m probeEnergy gamma := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV
    continuumBornRARadialIntegralUVLimit continuumBornRAWeakDisorderArctanMass
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength
      v hbar gamma hvelocity hhbar,
    continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar,
    continuumBornRADenominatorWidth_weakDisorderStrength
      v m probeEnergy hbar gamma hvelocity hhbar]
  field_simp [hvelocity, hhbar, hgamma, ne_of_gt hsum, Real.pi_ne_zero]

/-- Exact infinite-cutoff transverse coefficient in repository orientation `Gᴿ σₓ Gᴬ` under the
weak-disorder parameterization. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV_weakDisorderStrength_eq
    (v m probeEnergy hbar gamma : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hgamma : gamma ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV
        v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      (2 * gamma * probeEnergy * m /
        (Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        continuumBornRAWeakDisorderArctanMass m probeEnergy gamma := by
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV
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

private theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorder_closed
    (v m probeEnergy hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (fun gamma : ℝ =>
        continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV
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
  exact (continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar (ne_of_gt hgamma_pos) hmetal).symm

/-- Metallic weak-disorder limit of the infinite-cutoff longitudinal one-rung coefficient.  The
limit is the canonical scalar rung coefficient already used by the fixed-cutoff transport bridge. -/
theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorder
    (v m probeEnergy hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (fun gamma : ℝ =>
        continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV
          v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy)) := by
  simpa [continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient] using
    tendsto_continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorder_closed
      v m probeEnergy hbar hvelocity hhbar hmetal

/-- Exact scaled transverse coefficient under the weak-disorder parameterization. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV_div_gamma_weakDisorderStrength_eq
    (v m probeEnergy hbar gamma : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hgamma : gamma ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV
        v m probeEnergy (continuumBornWeakDisorderStrength v hbar gamma) hbar / gamma =
      (2 * probeEnergy * m /
        (Real.pi * (probeEnergy ^ 2 + m ^ 2))) *
        continuumBornRAWeakDisorderArctanMass m probeEnergy gamma := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar hgamma hmetal]
  field_simp [hgamma]

/-- Metallic weak-disorder limit of the leading transverse one-rung coefficient.  The unscaled
`σᵧ` coefficient is `O(γ)`; the limit below exposes its positive repository-orientation coefficient. -/
theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV_div_gamma_weakDisorder
    (v m probeEnergy hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (fun gamma : ℝ =>
        continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV
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
  exact (continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV_div_gamma_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar (ne_of_gt hgamma_pos) hmetal).symm

end

end AnomalousHall.MassiveDirac

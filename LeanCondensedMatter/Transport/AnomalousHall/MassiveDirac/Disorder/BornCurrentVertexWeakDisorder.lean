import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the Born retarded-advanced current rung

This Phase 5 consumer combines the Born-dressed radial kernels with the exact radial integral from
`BornCurrentVertexIntegral.lean`.  It first identifies the complex radial integrals with real-valued
one-rung coefficients including the scalar-disorder line and physical momentum measure.  The radial
cutoff is then removed at fixed positive Born width.

Finally the continuum coupling is parameterized by

```text
W(γ) = 4 γ ℏ² v²,
```

which exactly inverts `continuumBornDampingScale`.  In the metallic regime `m² < ε²`, the
longitudinal one-rung coefficient tends to

```text
(ε² - m²) / (2 (ε² + m²)),
```

while the transverse coefficient in repository orientation `Gᴿ σₓ Gᴬ` is `O(γ)` with

```text
Y₁ / γ → 2 ε m / (ε² + m²).
```

No ladder fixed point, transport-lifetime identification, Kubo–Středa insertion, Ward claim, or
conductivity theorem is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory
open QuantumTheory.Transport
open scoped Interval

private def continuumBornRACurrentRungRadialXIntegrandReal
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
      (2 * Real.pi *
        (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2))) *
    (p / continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar)

private def continuumBornRACurrentRungRadialYIntegrandReal
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
      (8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
        probeEnergy * m)) *
    (p / continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar)

private theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq_ofReal
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
        v m p probeEnergy disorderStrength hbar =
      (continuumBornRACurrentRungRadialXIntegrandReal
        v m p probeEnergy disorderStrength hbar : ℂ) := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq_closed]
  unfold continuumBornRACurrentRungRadialXIntegrandReal
  push_cast
  ring

private theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq_ofReal
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
        v m p probeEnergy disorderStrength hbar =
      (continuumBornRACurrentRungRadialYIntegrandReal
        v m p probeEnergy disorderStrength hbar : ℂ) := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq_closed]
  unfold continuumBornRACurrentRungRadialYIntegrandReal
  push_cast
  ring

/-- Finite-cutoff full `σₓ` one-rung coefficient, including the scalar-disorder line and physical
momentum measure fixed in `BornCurrentVertexRadial.lean`. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    (2 * Real.pi *
      (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2)) *
    finiteCutoffContinuumBornRARadialIntegral
      v m probeEnergy disorderStrength hbar pMax

/-- Finite-cutoff full `σᵧ` one-rung coefficient in repository orientation `Gᴿ σₓ Gᴬ`. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
    (8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
      probeEnergy * m) *
    finiteCutoffContinuumBornRARadialIntegral
      v m probeEnergy disorderStrength hbar pMax

/-- The finite-cutoff complex `σₓ` radial current-rung integral is exactly the cast of its real
coefficient. -/
theorem integral_continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
        v m p probeEnergy disorderStrength hbar) =
      (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) := by
  calc
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
        v m p probeEnergy disorderStrength hbar) =
        ∫ p in (0 : ℝ)..pMax,
          (continuumBornRACurrentRungRadialXIntegrandReal
            v m p probeEnergy disorderStrength hbar : ℂ) := by
      apply intervalIntegral.integral_congr
      intro p _
      exact continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq_ofReal
        v m p probeEnergy disorderStrength hbar
    _ = (((∫ p in (0 : ℝ)..pMax,
        continuumBornRACurrentRungRadialXIntegrandReal
          v m p probeEnergy disorderStrength hbar) : ℝ) : ℂ) := by
      exact @intervalIntegral.integral_ofReal
        (0 : ℝ) pMax volume
        (continuumBornRACurrentRungRadialXIntegrandReal
          v m · probeEnergy disorderStrength hbar)
    _ = (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) := by
      congr 1
      unfold continuumBornRACurrentRungRadialXIntegrandReal
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        finiteCutoffContinuumBornRARadialIntegral
      rw [intervalIntegral.integral_const_mul]

/-- The finite-cutoff complex `σᵧ` radial current-rung integral is exactly the cast of its real
coefficient. -/
theorem integral_continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
        v m p probeEnergy disorderStrength hbar) =
      (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) := by
  calc
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
        v m p probeEnergy disorderStrength hbar) =
        ∫ p in (0 : ℝ)..pMax,
          (continuumBornRACurrentRungRadialYIntegrandReal
            v m p probeEnergy disorderStrength hbar : ℂ) := by
      apply intervalIntegral.integral_congr
      intro p _
      exact continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq_ofReal
        v m p probeEnergy disorderStrength hbar
    _ = (((∫ p in (0 : ℝ)..pMax,
        continuumBornRACurrentRungRadialYIntegrandReal
          v m p probeEnergy disorderStrength hbar) : ℝ) : ℂ) := by
      exact @intervalIntegral.integral_ofReal
        (0 : ℝ) pMax volume
        (continuumBornRACurrentRungRadialYIntegrandReal
          v m · probeEnergy disorderStrength hbar)
    _ = (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) := by
      congr 1
      unfold continuumBornRACurrentRungRadialYIntegrandReal
        finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient
        finiteCutoffContinuumBornRARadialIntegral
      rw [intervalIntegral.integral_const_mul]

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

/-- The finite-cutoff `σₓ` one-rung coefficient converges to the infinite-cutoff coefficient at
fixed positive Born width. -/
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
  have hconst :
      Tendsto
        (fun _pMax : ℝ =>
          continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
            (2 * Real.pi *
              (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
              (probeEnergy ^ 2 - m ^ 2)))
        atTop
        (nhds
          (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
            (2 * Real.pi *
              (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
              (probeEnergy ^ 2 - m ^ 2)))) := tendsto_const_nhds
  simpa [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient,
    continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV] using hconst.mul hradial

/-- The finite-cutoff `σᵧ` one-rung coefficient converges to the infinite-cutoff coefficient at
fixed positive Born width. -/
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
  have hconst :
      Tendsto
        (fun _pMax : ℝ =>
          continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
            (8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
              probeEnergy * m))
        atTop
        (nhds
          (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
            (8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
              probeEnergy * m))) := tendsto_const_nhds
  simpa [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungYCoefficient,
    continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV] using hconst.mul hradial

/-- Continuum disorder strength corresponding exactly to a chosen Born damping scale `γ`. -/
def continuumBornWeakDisorderStrength (v hbar gamma : ℝ) : ℝ :=
  4 * gamma * hbar ^ 2 * v ^ 2

/-- The weak-disorder parameterization `W(γ) = 4 γ ℏ² v²` exactly inverts
`continuumBornDampingScale`. -/
theorem continuumBornDampingScale_weakDisorderStrength
    (v hbar gamma : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornDampingScale v (continuumBornWeakDisorderStrength v hbar gamma) hbar = gamma := by
  unfold continuumBornDampingScale continuumBornWeakDisorderStrength
  field_simp [hvelocity, hhbar] <;> ring

/-- Under the weak-disorder parameterization, the RA denominator width is `2γ(ε²+m²)`. -/
theorem continuumBornRADenominatorWidth_weakDisorderStrength
    (v m probeEnergy hbar gamma : ℝ) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) :
    continuumBornRADenominatorWidth v m probeEnergy
        (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      2 * gamma * (probeEnergy ^ 2 + m ^ 2) := by
  unfold continuumBornRADenominatorWidth
  rw [continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar]

/-- The full continuum current-rung prefactor under `W(γ) = 4γℏ²v²`. -/
theorem continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength
    (v hbar gamma : ℝ) (hhbar : hbar ≠ 0) :
    continuumBornRetardedAdvancedCurrentRungPrefactor
        (continuumBornWeakDisorderStrength v hbar gamma) hbar =
      gamma * v ^ 2 / Real.pi ^ 2 := by
  unfold continuumBornRetardedAdvancedCurrentRungPrefactor
    continuumBornWeakDisorderStrength momentumMeasurePrefactor
  field_simp [hhbar, Real.pi_ne_zero] <;> ring

/-- Arctangent mass controlling the metallic weak-disorder limit after the radial cutoff has been
removed. -/
def continuumBornRAWeakDisorderArctanMass
    (m probeEnergy gamma : ℝ) : ℝ :=
  Real.pi / 2 +
    Real.arctan
      (((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
        (2 * gamma * (probeEnergy ^ 2 + m ^ 2)))

/-- Exact infinite-cutoff longitudinal one-rung coefficient after parameterizing the disorder by
its damping scale `γ`. -/
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
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength v hbar gamma hhbar,
    continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar,
    continuumBornRADenominatorWidth_weakDisorderStrength
      v m probeEnergy hbar gamma hvelocity hhbar]
  field_simp [hvelocity, hhbar, hgamma, ne_of_gt hsum, Real.pi_ne_zero] <;> ring

/-- Exact infinite-cutoff transverse one-rung coefficient in repository orientation `Gᴿ σₓ Gᴬ`
after parameterizing the disorder by `γ`. -/
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
  rw [continuumBornRetardedAdvancedCurrentRungPrefactor_weakDisorderStrength v hbar gamma hhbar,
    continuumBornDampingScale_weakDisorderStrength v hbar gamma hvelocity hhbar,
    continuumBornRADenominatorWidth_weakDisorderStrength
      v m probeEnergy hbar gamma hvelocity hhbar]
  field_simp [hvelocity, hhbar, hgamma, ne_of_gt hsum, Real.pi_ne_zero] <;> ring

/-- In the metallic regime the weak-disorder arctangent mass tends to `π` as `γ → 0⁺`. -/
theorem tendsto_continuumBornRAWeakDisorderArctanMass_zero
    (m probeEnergy : ℝ) (hmetal : m ^ 2 < probeEnergy ^ 2) :
    Tendsto
      (continuumBornRAWeakDisorderArctanMass m probeEnergy)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) := by
  have hdelta : 0 < probeEnergy ^ 2 - m ^ 2 := sub_pos.mpr hmetal
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  let distance : ℝ := (probeEnergy ^ 2 - m ^ 2) /
    (2 * (probeEnergy ^ 2 + m ^ 2))
  have hdistance : 0 < distance := by
    dsimp [distance]
    positivity
  have hinv : Tendsto (fun gamma : ℝ => gamma⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hlarge : Tendsto (fun gamma : ℝ => distance * gamma⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => distance)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds distance)).pos_mul_atTop hdistance hinv
  have hgamma0 : Tendsto (fun gamma : ℝ => gamma)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact tendsto_id.mono_left inf_le_left
  have hsmall : Tendsto (fun gamma : ℝ => -(distance * gamma))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hscaled :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => distance)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds distance)).mul hgamma0
    simpa using hscaled.neg
  have hargRhs : Tendsto
      (fun gamma : ℝ => distance * gamma⁻¹ + -(distance * gamma))
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Tendsto.atTop_add hlarge hsmall
  have harg : Tendsto
      (fun gamma : ℝ =>
        ((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
          (2 * gamma * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    refine hargRhs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with gamma hgamma
    have hgamma_pos : 0 < gamma := by
      simpa only [Set.mem_Ioi] using hgamma
    dsimp [distance]
    field_simp [ne_of_gt hgamma_pos, ne_of_gt hsum] <;> ring
  have harctanWithin := Real.tendsto_arctan_atTop.comp harg
  have harctan : Tendsto
      (fun gamma : ℝ =>
        Real.arctan
          (((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
            (2 * gamma * (probeEnergy ^ 2 + m ^ 2))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    simpa [Function.comp_def] using tendsto_nhds_of_tendsto_nhdsWithin harctanWithin
  have hhalf : Tendsto (fun _gamma : ℝ => Real.pi / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := tendsto_const_nhds
  have hmass := hhalf.add harctan
  have hpi : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
  change Tendsto
    (fun gamma : ℝ =>
      Real.pi / 2 +
        Real.arctan
          (((1 - gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2)) /
            (2 * gamma * (probeEnergy ^ 2 + m ^ 2))))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi)
  simpa [hpi] using hmass

/-- Metallic weak-disorder limit of the longitudinal one-rung coefficient. -/
theorem tendsto_continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorder
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
  have hfactorConst : Tendsto
      (fun _gamma : ℝ =>
        (probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((probeEnergy ^ 2 - m ^ 2) /
        (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))) := tendsto_const_nhds
  have hfactor0 := hshape.mul hfactorConst
  have hfactor : Tendsto
      (fun gamma : ℝ =>
        (1 + gamma ^ 2) * (probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((probeEnergy ^ 2 - m ^ 2) /
        (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2)))) := by
    simpa [div_eq_mul_inv, mul_assoc] using hfactor0
  have hmass := tendsto_continuumBornRAWeakDisorderArctanMass_zero
    m probeEnergy hmetal
  have hprod := hfactor.mul hmass
  have htarget :
      ((probeEnergy ^ 2 - m ^ 2) /
          (2 * Real.pi * (probeEnergy ^ 2 + m ^ 2))) * Real.pi =
        (probeEnergy ^ 2 - m ^ 2) /
          (2 * (probeEnergy ^ 2 + m ^ 2)) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hsum] <;> ring
  rw [htarget] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with gamma hgamma
  have hgamma_pos : 0 < gamma := by
    simpa only [Set.mem_Ioi] using hgamma
  exact (continuumBornRetardedAdvancedPauliXCurrentRungXCoefficientUV_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar (ne_of_gt hgamma_pos) hmetal).symm

/-- Exact scaled transverse coefficient under the weak-disorder parameterization.  This keeps the
positive sign specific to the repository orientation `Gᴿ σₓ Gᴬ`. -/
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
  field_simp [hgamma] <;> ring

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
  have hconst : Tendsto
      (fun _gamma : ℝ =>
        2 * probeEnergy * m /
          (Real.pi * (probeEnergy ^ 2 + m ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * probeEnergy * m /
        (Real.pi * (probeEnergy ^ 2 + m ^ 2)))) := tendsto_const_nhds
  have hmass := tendsto_continuumBornRAWeakDisorderArctanMass_zero
    m probeEnergy hmetal
  have hprod := hconst.mul hmass
  have htarget :
      (2 * probeEnergy * m /
          (Real.pi * (probeEnergy ^ 2 + m ^ 2))) * Real.pi =
        2 * probeEnergy * m / (probeEnergy ^ 2 + m ^ 2) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hsum] <;> ring
  rw [htarget] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with gamma hgamma
  have hgamma_pos : 0 < gamma := by
    simpa only [Set.mem_Ioi] using hgamma
  exact (continuumBornRetardedAdvancedPauliXCurrentRungYCoefficientUV_div_gamma_weakDisorderStrength_eq
    v m probeEnergy hbar gamma hvelocity hhbar (ne_of_gt hgamma_pos) hmetal).symm

end

end AnomalousHall.MassiveDirac

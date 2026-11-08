import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialScalarGenerator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornDysonShift
import Mathlib.Analysis.Calculus.Deriv.Star

set_option linter.style.header false

/-!
# Retarded/advanced scalar Fourier-generator conjugation

At finite broadening and momentum cutoff, the scalar radial Fourier
generator of the *actual* Born-Dyson propagator has only one independent
causal branch: the advanced generator is the complex conjugate of the
retarded generator at the same real-space radius. This uses the model's
already-proved finite-cutoff Dyson denominator star symmetry and the
reality of the zeroth angular Fourier kernel.

The conjugation is preserved after differentiating in the **real**
radial coordinate. These are the finite-regulator symmetry inputs
needed to reduce the physical crossed X Green minors to one causal
Fourier generator before selecting its Hankel/Bessel boundary.

This module does not send any regulator or Fourier cutoff to infinity
and does not identify the finite Born self-energy with its divergent
unrenormalized UV limit.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval ComplexConjugate

/-- Advanced scalar Green Fourier generator is exactly the complex conjugate
of its retarded partner at every finite cutoff. In particular this statement
includes the momentum measure and the cutoff-dependent self-energy at the
*same* cutoff, rather than freezing spectral parameters. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_conj
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) :
    conj (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius) =
    finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius := by
  unfold finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
  rw [map_mul]
  simp only [Complex.conj_ofReal]
  have hmove :
      conj (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          polarFourierZerothAngularKernel (p * radius / hbar)) =
        ∫ p in (0 : ℝ)..pMax,
          conj ((p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
            polarFourierZerothAngularKernel (p * radius / hbar)) := by
    simpa using
      ((Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
        (f := fun p : ℝ =>
          (p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
            polarFourierZerothAngularKernel (p * radius / hbar))
        (a := (0 : ℝ)) (b := pMax)).symm
  rw [hmove]
  congr 1
  apply intervalIntegral.integral_congr
  intro p _
  simp only [map_mul, map_inv, Complex.conj_ofReal,
    polarFourierZerothAngularKernel_conj]
  have hden := star_finiteCutoffContinuumBornDysonDenominator
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax hbroadening
  change conj (finiteCutoffContinuumBornDysonDenominator
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax) =
    finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax at hden
  rw [hden]

/-- The advanced and retarded scalar radial derivatives are also conjugate.
The domain variable is real, so conjugation is a linear operation over the
domain field: this is *not* complex differentiation of a nonholomorphic
conjugate function. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_deriv_conj
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) :
    deriv (fun r : ℝ =>
      finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius =
    conj (deriv (fun r : ℝ =>
      finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius) := by
  have hfun :
      (fun r : ℝ =>
        finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax r) =
      (fun r : ℝ => star (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax r)) := by
    funext r
    exact (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_conj
      v m probeEnergy broadening disorderStrength hbar pMax r hbroadening).symm
  rw [hfun]
  exact deriv.star


/-- The radial Pauli-x retarded/advanced Green components are
**anti**-conjugates at the *same signed real-space radius*.
The minus sign is the parity of the first Fourier harmonic.
This is an exact physical Born-Dyson identity at finite regulator. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauli_x_conj_eq_neg_advanced
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    conj (finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .x
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius) =
      -finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .x
        .advanced v m probeEnergy broadening disorderStrength hbar pMax radius := by
  rw [finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_eq_deriv_generator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_eq_deriv_generator
    .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [← finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_deriv_conj
    v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening]
  ring

end

end QuantumTheory.Models.MassiveDirac

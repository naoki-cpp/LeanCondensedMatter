import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Denominator forms of finite-broadening dressed Středa surfaces

This module specializes the source-indexed finite-`η` massive-Dirac Středa radial coefficient to
explicit Born-Dyson denominator forms. Source `.x` is the longitudinal component and retains the
bare RR/AA same-side remainder. Source `.y` is the ordered `xy` component and uses the shared
retarded-advanced denominator product after its same-side contribution vanishes.

The algebraic radial coefficient and Středa values are total and carry no ladder-regularity proof.
Regularity remains a separate condition for interpreting the solved vector as the physical ladder
fixed point. No disorder, external-broadening, or ultraviolet limit is taken, and the ordered `xy`
component remains distinct from the antisymmetric Hall projection.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- The source-`.x` finite-`η` dressed Středa angular coefficient in explicit denominator form.
The first term is the dressed RA contribution; the second retains the bare RR/AA same-side
remainder with the retarded and advanced denominators kept separate. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_x_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .x e v m p probeEnergy broadening disorderStrength hbar pMax =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
      let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
        v m probeEnergy broadening disorderStrength hbar pMax;
      let eR := finiteCutoffContinuumBornEffectiveEnergy
        .retarded v m probeEnergy broadening disorderStrength hbar pMax;
      let massR := finiteCutoffContinuumBornEffectiveMass
        .retarded v m probeEnergy broadening disorderStrength hbar pMax;
      let dR := finiteCutoffContinuumBornDysonDenominator
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax;
      let eA := finiteCutoffContinuumBornEffectiveEnergy
        .advanced v m probeEnergy broadening disorderStrength hbar pMax;
      let massA := finiteCutoffContinuumBornEffectiveMass
        .advanced v m probeEnergy broadening disorderStrength hbar pMax;
      let dA := finiteCutoffContinuumBornDysonDenominator
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax;
      (((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
        (dR⁻¹ * dA⁻¹ *
            ((eR * eA - massR * massA) * solved .x -
              Complex.I * (eA * massR - eR * massA) * solved .y) -
          (1 / 2 : ℂ) *
            (dR⁻¹ ^ 2 * (eR ^ 2 - massR ^ 2) +
              dA⁻¹ ^ 2 * (eA ^ 2 - massA ^ 2))) := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  simp only [inPlaneLadderAction_apply_x, Matrix.transpose_apply,
    inPlaneRotationMatrix_apply_x_x, inPlaneRotationMatrix_apply_y_x,
    mul_one, mul_zero, sub_zero]
  unfold pauliRungAngularXCoefficient pauliRungAngularYCoefficient
    finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornDysonPauliCoefficient pauliAxisComponent
  have hpi : (((4 * Real.pi : ℝ) : ℂ)) =
      (2 : ℂ) * (((2 * Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hpi]
  ring

/-- Numerator multiplying the common finite-`η` RA Born-Dyson denominator in the source-`.y`
ordered transverse surface trace. -/
def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
      .x .x v m probeEnergy broadening disorderStrength hbar pMax * solved .y +
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
      .y .x v m probeEnergy broadening disorderStrength hbar pMax * solved .x

/-- The source-`.y` finite-`η` dressed ordered `xy` angular coefficient has one explicit common RA
Born-Dyson denominator. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_y_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .y e v m p probeEnergy broadening disorderStrength hbar pMax =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
      -(((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
          v m probeEnergy broadening disorderStrength hbar pMax := by
  calc
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        .y e v m p probeEnergy broadening disorderStrength hbar pMax =
      (let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
       let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
         v m probeEnergy broadening disorderStrength hbar pMax;
       let x := finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
         .x .x v m p probeEnergy broadening disorderStrength hbar pMax;
       let y := finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
         .y .x v m p probeEnergy broadening disorderStrength hbar pMax;
       (2 : ℂ) * q ^ 2 * (-(x * solved .y + y * solved .x))) := by
      unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
      dsimp only
      unfold finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient
      simp only [inPlaneLadderAction_apply_x, Matrix.transpose_apply,
        inPlaneRotationMatrix_apply_x_x, inPlaneRotationMatrix_apply_x_y,
        inPlaneRotationMatrix_apply_y_x, inPlaneRotationMatrix_apply_y_y,
        mul_one, mul_zero, neg_zero, pauliRungAngularYCoefficient, sub_self]
      ring
    _ = _ := by
      dsimp only
      rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm
            .x .x v m p probeEnergy broadening disorderStrength hbar pMax,
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm
            .y .x v m p probeEnergy broadening disorderStrength hbar pMax]
      unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
      dsimp only
      have hpi : (((4 * Real.pi : ℝ) : ℂ)) =
          (2 : ℂ) * (((2 * Real.pi : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [hpi]
      ring

/-- The ordered `xy` radial Hall-surface integrand is the source-`.y` Středa radial response in
explicit common RA Born-Dyson denominator form. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .y e v m p probeEnergy broadening disorderStrength hbar pMax =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
      (p : ℂ) *
        (-(((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
            v m probeEnergy broadening disorderStrength hbar pMax) := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_y_eq_denominatorForm]

end

end QuantumTheory.Transport.Models.MassiveDirac

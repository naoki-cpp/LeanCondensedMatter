import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Denominator forms of finite-broadening dressed Středa surfaces

This module rewrites the angularly reduced finite-`η` massive-Dirac Středa surface coefficients into
explicit Born-Dyson denominator forms. The longitudinal source-`.x` form retains both the dressed RA
term and the nonzero bare-source RR/AA same-side remainder. The ordered source-`.y` Hall form uses the
shared retarded-advanced denominator product.

The shared ladder-regularity proof is threaded through the dressed-response objects unchanged. No
disorder, external-broadening, or ultraviolet limit is taken, and the ordered `xy` component remains
distinct from the antisymmetric Hall projection.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- The finite-`η` dressed longitudinal Středa angular coefficient in explicit denominator form.
The first term is the dressed RA contribution; the second retains the bare RR/AA same-side
remainder with the retarded and advanced denominators kept separate. -/
theorem finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) :
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        e v m p probeEnergy broadening disorderStrength hbar pMax hdet =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
      let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
        .x v m probeEnergy broadening disorderStrength hbar pMax;
      let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
        .y v m probeEnergy broadening disorderStrength hbar pMax;
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
            ((eR * eA - massR * massA) * alpha -
              Complex.I * (eA * massR - eR * massA) * beta) -
          (1 / 2 : ℂ) *
            (dR⁻¹ ^ 2 * (eR ^ 2 - massR ^ 2) +
              dA⁻¹ ^ 2 * (eA ^ 2 - massA ^ 2))) := by
  unfold finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  unfold pauliRungAngularXCoefficient pauliRungAngularYCoefficient
    finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornDysonPauliCoefficient pauliAxisComponent
  have hpi : (((4 * Real.pi : ℝ) : ℂ)) =
      (2 : ℂ) * (((2 * Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hpi]
  ring

/-- Numerator multiplying the common finite-`η` RA Born-Dyson denominator in the dressed ordered
`xy` Hall-surface trace. The first term multiplies the solved transverse coefficient `β`; the
orientation-sensitive second term multiplies the solved longitudinal coefficient `α`. -/
def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (_hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) : ℂ :=
  finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
      .x .x v m probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonLadderSolvedCoefficient
      .y v m probeEnergy broadening disorderStrength hbar pMax +
  finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
      .y .x v m probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonLadderSolvedCoefficient
      .x v m probeEnergy broadening disorderStrength hbar pMax

/-- The finite-`η` dressed ordered `xy` Hall-surface angular coefficient has one explicit common RA
Born-Dyson denominator. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        e v m p probeEnergy broadening disorderStrength hbar pMax hdet =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
      -(((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
          v m probeEnergy broadening disorderStrength hbar pMax hdet := by
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm
        .x .x v m p probeEnergy broadening disorderStrength hbar pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm
        .y .x v m p probeEnergy broadening disorderStrength hbar pMax]
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
  have hpi : (((4 * Real.pi : ℝ) : ℂ)) =
      (2 : ℂ) * (((2 * Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hpi]
  ring

/-- The ordered `xy` radial Hall-surface integrand is the source-`.y` Středa radial response in
explicit common RA Born-Dyson denominator form. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
        .y e v m p probeEnergy broadening disorderStrength hbar pMax hdet =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ));
      (p : ℂ) *
        (-(((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
            v m probeEnergy broadening disorderStrength hbar pMax hdet) := by
  rw [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq,
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_eq_denominatorForm]

end

end QuantumTheory.Transport.Models.MassiveDirac

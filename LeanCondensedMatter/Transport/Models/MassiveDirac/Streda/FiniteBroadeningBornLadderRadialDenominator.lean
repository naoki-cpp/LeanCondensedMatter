import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Common-denominator form of the finite-broadening dressed Hall surface

This module rewrites the angularly reduced finite-`η` ordered `xy` Hall-surface coefficient from the
direction-indexed in-plane rung matrix into the shared retarded-advanced Born-Dyson denominator
form. The shared ladder-regularity proof is threaded through the dressed-response objects unchanged.

No disorder, external-broadening, or ultraviolet limit is taken. The result remains the ordered
`x`-measured/`y`-source Středa response component rather than the antisymmetric Hall projection.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

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

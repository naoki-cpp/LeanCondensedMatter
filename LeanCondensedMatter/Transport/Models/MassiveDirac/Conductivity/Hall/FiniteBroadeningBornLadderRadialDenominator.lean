import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Common-denominator form of the finite-broadening dressed Hall surface

This module rewrites the angularly reduced finite-`η` ordered `xy` Hall-surface coefficient from the
canonical rung pair `(X,Y)` into the shared retarded-advanced Born-Dyson denominator form.

No disorder, external-broadening, or ultraviolet limit is taken.  The result remains the ordered
`x`-measured/`y`-source conductivity component rather than the antisymmetric Hall projection.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Numerator multiplying the common finite-`η` RA Born-Dyson denominator in the dressed ordered
`xy` Hall-surface trace.  The first term multiplies the solved transverse coefficient `β`; the
orientation-sensitive second term multiplies the solved longitudinal coefficient `α`. -/
def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator
      v m probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax +
  finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator
      v m probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax

/-- The finite-`η` dressed ordered `xy` Hall-surface angular coefficient has one explicit common RA
Born-Dyson denominator. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
        e v m p probeEnergy broadening disorderStrength hbar pMax =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
      -(((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient
  dsimp only
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_eq_denominatorForm,
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_eq_denominatorForm]
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
  ring

/-- The #2011 radial Hall-surface integrand is the polar Jacobian multiplying the explicit common
RA Born-Dyson denominator form. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand
        e v m p probeEnergy broadening disorderStrength hbar pMax =
      let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
      (p : ℂ) *
        (-(((4 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
            v m probeEnergy broadening disorderStrength hbar pMax) := by
  rw [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq,
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_eq_denominatorForm]

end

end QuantumTheory.Transport.Models.MassiveDirac

import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson radial rung denominator form

This module exposes the numerators already implicit in the finite-`η` Born-Dyson in-plane rung
coefficients and reduces the canonical `X/Y` coefficients over the shared propagator-level RA
denominator product. No disorder, external-broadening, or ultraviolet limit is taken.

The repository ordering remains `Gᴿ Γ Gᴬ`. In that orientation the transverse numerator is
`i (E_A M_R - E_R M_A)`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Numerator of the longitudinal `X` coefficient before the common RA denominator is attached. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax -
  finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax

/-- Orientation-sensitive numerator of the transverse `Y` coefficient for repository ordering
`Gᴿ Γ Gᴬ`, before the common RA denominator is attached. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  Complex.I *
    (finiteCutoffContinuumBornEffectiveEnergy
        .advanced v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMass
        .retarded v m probeEnergy broadening disorderStrength hbar pMax -
    finiteCutoffContinuumBornEffectiveEnergy
        .retarded v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMass
        .advanced v m probeEnergy broadening disorderStrength hbar pMax)

/-- The common finite-`η` RA denominator product is nonzero whenever the existing Born-Dyson
invertibility hypotheses hold. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_ne_zero
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
      v m p probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
  exact mul_ne_zero
    (finiteCutoffContinuumBornDysonDenominator_ne_zero
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax)
    (finiteCutoffContinuumBornDysonDenominator_ne_zero
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax)

/-- Closed common-denominator form of the full-angle longitudinal finite-`η` Born-Dyson rung
coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient_eq_denominatorForm
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
        v m p probeEnergy broadening disorderStrength hbar pMax =
      (((2 * Real.pi : ℝ) : ℂ)) *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
    pauliRungAngularXCoefficient
    finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornDysonZCoefficient
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularXNumerator
  simp [mul_inv_rev]
  ring

/-- Closed common-denominator form of the full-angle orientation-sensitive finite-`η` Born-Dyson
rung coefficient. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient_eq_denominatorForm
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
        v m p probeEnergy broadening disorderStrength hbar pMax =
      (((2 * Real.pi : ℝ) : ℂ)) *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
    pauliRungAngularYCoefficient
    finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornDysonZCoefficient
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    finiteCutoffContinuumBornDysonRetardedAdvancedAngularYNumerator
  simp [mul_inv_rev]
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac

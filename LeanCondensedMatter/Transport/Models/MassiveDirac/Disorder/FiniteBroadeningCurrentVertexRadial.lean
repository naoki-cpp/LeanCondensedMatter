import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson radial rung denominator form

This module exposes the numerator already implicit in the finite-`η` Born-Dyson in-plane rung
coefficient matrix and reduces every direction-indexed entry over the shared propagator-level RA
denominator product. No disorder, external-broadening, or ultraviolet limit is taken.

The repository ordering remains `Gᴿ Γ Gᴬ`. In that orientation the transverse numerator is
`i (E_A M_R - E_R M_A)`, and the full in-plane matrix has the form `[[X,-Y],[Y,X]]`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Numerator of entry `(i,j)` of the finite-`η` Born-Dyson in-plane rung before the common RA
denominator is attached. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
    (i j : Direction2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneRotationCoefficient
    (finiteCutoffContinuumBornEffectiveEnergy
        .retarded v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveEnergy
        .advanced v m probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornEffectiveMass
        .retarded v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornEffectiveMass
        .advanced v m probeEnergy broadening disorderStrength hbar pMax)
    (Complex.I *
      (finiteCutoffContinuumBornEffectiveEnergy
          .advanced v m probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornEffectiveMass
          .retarded v m probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornEffectiveEnergy
          .retarded v m probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornEffectiveMass
          .advanced v m probeEnergy broadening disorderStrength hbar pMax))
    i j

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

/-- Closed common-denominator form of every entry `(i,j)` of the full-angle finite-`η` Born-Dyson
retarded-advanced rung. Coordinate-specific consumers specialize `i` and `j`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm
    (i j : Direction2)
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    inPlaneRotationCoefficient
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient
          v m p probeEnergy broadening disorderStrength hbar pMax)
        i j =
      (((2 * Real.pi : ℝ) : ℂ)) *
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator
          i j v m probeEnergy broadening disorderStrength hbar pMax := by
  cases i <;> cases j <;>
    simp [inPlaneRotationCoefficient,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularXCoefficient,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularYCoefficient,
      pauliRungAngularXCoefficient, pauliRungAngularYCoefficient,
      finiteCutoffContinuumBornDysonScalarCoefficient,
      finiteCutoffContinuumBornDysonZCoefficient,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct,
      mul_inv_rev] <;>
    ring

end

end QuantumTheory.Transport.Models.MassiveDirac

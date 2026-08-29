import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexRadial

set_option linter.style.header false

/-!
# Finite-cutoff Born retarded-advanced current rung

This module integrates the one-dimensional Born-dressed radial Green-product kernels proved in
`BornCurrentVertexRadial.lean`.  The angular Pauli algebra, the actual `Gᴿ σₓ Gᴬ` full-angle
identity, the retarded-advanced denominator reduction, and the physical `p dp` Jacobian are all
consumed from that module rather than reproved here.

The finite-cutoff coefficients below contain the angular-integrated Green product and radial
integration only.  They intentionally do not attach the external scalar-disorder line or the
physical momentum-measure prefactor, which remain explicit in `BornCurrentVertexRadial.lean`.

No radial closed-form evaluation, weak-disorder/on-shell limit, ladder resummation, transport-
lifetime identification, Ward/SCBA statement, Kubo insertion, or conductivity theorem is made
here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open scoped Interval

/-- Finite-cutoff radial `σₓ` Green-product coefficient after the proved Born angular reduction. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXRadialXIntegrand
      v m p probeEnergy disorderStrength hbar

/-- Finite-cutoff radial orientation-sensitive `σᵧ` Green-product coefficient after the proved Born
angular reduction. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
      v m p probeEnergy disorderStrength hbar

/-- The finite-cutoff `σₓ` coefficient is the integral of the closed real-denominator kernel from
`BornCurrentVertexRadial.lean`. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient_eq_closed
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
        v m probeEnergy disorderStrength hbar pMax =
      ∫ p in (0 : ℝ)..pMax,
        (((2 * Real.pi * p *
            (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
          (continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  apply intervalIntegral.integral_congr
  intro p _
  exact continuumBornRetardedAdvancedPauliXRadialXIntegrand_eq_closed
    v m p probeEnergy disorderStrength hbar

/-- The finite-cutoff `σᵧ` coefficient is the integral of the closed real-denominator kernel from
`BornCurrentVertexRadial.lean`. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient_eq_closed
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
        v m probeEnergy disorderStrength hbar pMax =
      ∫ p in (0 : ℝ)..pMax,
        (((8 * Real.pi * p * continuumBornDampingScale v disorderStrength hbar *
            probeEnergy * m : ℝ) : ℂ)) *
          (continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  apply intervalIntegral.integral_congr
  intro p _
  exact continuumBornRetardedAdvancedPauliXRadialYIntegrand_eq_closed
    v m p probeEnergy disorderStrength hbar

/-- The orientation-sensitive radial `σᵧ` Green-product kernel vanishes in the massless model. -/
@[simp] theorem continuumBornRetardedAdvancedPauliXRadialYIntegrand_massless
    (v p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
      v 0 p probeEnergy disorderStrength hbar = 0 := by
  rw [continuumBornRetardedAdvancedPauliXRadialYIntegrand_eq_closed]
  simp

/-- The finite-cutoff orientation-sensitive `σᵧ` coefficient vanishes in the massless model. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient_massless
    (v probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
      v 0 probeEnergy disorderStrength hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient]

/-- Finite-cutoff in-plane Pauli package for the Born-dressed RA Green-product rung, before the
external scalar-disorder line and physical momentum-measure prefactor are attached. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
      v m probeEnergy disorderStrength hbar pMax • matrixOperator sigmaX +
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
      v m probeEnergy disorderStrength hbar pMax • matrixOperator sigmaY

/-- In the massless model the finite-cutoff Born-dressed RA Green-product rung is purely `σₓ`. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung_massless
    (v probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung
        v 0 probeEnergy disorderStrength hbar pMax =
      finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
          v 0 probeEnergy disorderStrength hbar pMax • matrixOperator sigmaX := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung]

/-- A zero radial cutoff gives a vanishing Born-dressed RA `σₓ` coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient]

/-- A zero radial cutoff gives a vanishing Born-dressed RA `σᵧ` coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient]

/-- A zero radial cutoff gives a vanishing packaged Born-dressed RA Green-product rung. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung]

end

end AnomalousHall.MassiveDirac

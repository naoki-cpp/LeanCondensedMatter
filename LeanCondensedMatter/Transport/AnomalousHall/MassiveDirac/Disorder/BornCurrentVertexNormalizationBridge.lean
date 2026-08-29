import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder

set_option linter.style.header false

/-!
# Normalized Born current-rung / Green-product bridge

This module records that the real finite-cutoff longitudinal current-rung coefficient introduced for
the weak-disorder analysis is exactly the previously integrated Born retarded-advanced Green-product
`σₓ` coefficient multiplied by the external scalar-disorder line and physical momentum-measure
prefactor.

The theorem is an exact identity inside the Born-dressed model.  It does not take a weak-disorder
limit, solve a ladder equation, or make a Kubo conductivity claim.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open scoped Interval

/-- The real normalized finite-cutoff `σₓ` current-rung coefficient is exactly the finite-cutoff
Green-product coefficient from `BornCurrentVertexFiniteCutoff` multiplied by the physical current-
rung prefactor from `BornCurrentVertexRadial`. -/
theorem coe_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_prefactor_mul_greenProduct
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
        finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
  rw [← Complex.ofRealLI_apply
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
        v m p probeEnergy disorderStrength hbar)]
  rw [← Complex.ofRealLI.intervalIntegral_comp_comm]
  rw [show
      (fun p : ℝ => Complex.ofRealLI
        (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal
          v m p probeEnergy disorderStrength hbar)) =
      (fun p : ℝ =>
        (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
          continuumBornRetardedAdvancedPauliXRadialXIntegrand
            v m p probeEnergy disorderStrength hbar) by
    funext p
    rw [Complex.ofRealLI_apply,
      coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrandReal]
    rfl]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- A zero radial cutoff gives a vanishing normalized longitudinal Born current-rung coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient]

end

end AnomalousHall.MassiveDirac

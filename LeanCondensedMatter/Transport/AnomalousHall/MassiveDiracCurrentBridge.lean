import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac
import LeanCondensedMatter.QuantumMechanics.SingleParticle.ChargeLikeCurrent

set_option linter.style.header false

/-!
# Massive-Dirac charge-current representative

The generic charge-like current theorem shows that the canonical corrected/conventional current for
`m = q I` has zero localization correction and reduces to `q v`.  This module records the concrete
matrix realization of that theorem for the massive-Dirac model.

It does not instantiate a real-space localization algebra inside one momentum fiber.  Instead it
identifies the model's existing current matrices with the canonical charge-like representative.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Canonical charge-like `x` current matrix obtained from `q vₓ` with electron charge `q = -e`. -/
noncomputable def canonicalChargeCurrentXMatrix (e v : ℝ) : Matrix2 :=
  (((-e : ℝ) : ℂ)) • velocityX v

/-- Canonical charge-like `y` current matrix obtained from `q vᵧ` with electron charge `q = -e`. -/
noncomputable def canonicalChargeCurrentYMatrix (e v : ℝ) : Matrix2 :=
  (((-e : ℝ) : ℂ)) • velocityY v

/-- The canonical charge-like `x` representative is exactly the historical massive-Dirac current
matrix `-e v σₓ`. -/
@[simp]
theorem canonicalChargeCurrentXMatrix_eq_currentX (e v : ℝ) :
    canonicalChargeCurrentXMatrix e v = currentX e v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalChargeCurrentXMatrix, currentX, velocityX, sigmaX]

/-- The canonical charge-like `y` representative is exactly the historical massive-Dirac current
matrix `-e v σᵧ`. -/
@[simp]
theorem canonicalChargeCurrentYMatrix_eq_currentY (e v : ℝ) :
    canonicalChargeCurrentYMatrix e v = currentY e v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalChargeCurrentYMatrix, currentY, velocityY, sigmaY]
  all_goals ring

end

end AnomalousHall.MassiveDirac

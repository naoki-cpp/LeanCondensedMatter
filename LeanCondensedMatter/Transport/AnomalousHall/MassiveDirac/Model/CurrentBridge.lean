import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic
import LeanCondensedMatter.QuantumMechanics.SingleParticle.ChargeLikeCurrent

set_option linter.style.header false

/-!
# Massive-Dirac charge-current representative

The generic charge-like current theorem shows that the canonical corrected/conventional current for
`m = q I` has zero localization correction and reduces to `q v`. This module records the concrete
matrix realization of that theorem for either in-plane direction of the massive-Dirac model.

It does not instantiate a real-space localization algebra inside one momentum fiber. Instead it
identifies the model's direction-indexed current matrix with the canonical charge-like representative.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Canonical charge-like current matrix `q v_μ` with electron charge `q = -e`. -/
noncomputable def canonicalChargeCurrentMatrix
    (direction : Direction2) (e v : ℝ) : Matrix2 :=
  (((-e : ℝ) : ℂ)) • velocity direction v

/-- The canonical charge-like representative is exactly the massive-Dirac current in either
in-plane direction. -/
@[simp]
theorem canonicalChargeCurrentMatrix_eq_current
    (direction : Direction2) (e v : ℝ) :
    canonicalChargeCurrentMatrix direction e v = current direction e v :=
  rfl

end

end AnomalousHall.MassiveDirac

import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Operator
import LeanCondensedMatter.QuantumMechanics.SingleParticle.ChargeLikeCurrent

set_option linter.style.header false

/-!
# Massive-Dirac charge-current representative

The generic charge-like current theorem shows that the canonical corrected/conventional current for
`m = q I` has zero localization correction and reduces to `q v`. This module records the concrete
massive-Dirac realization at both the matrix and bounded-operator levels for either in-plane
direction.

It does not instantiate a real-space localization algebra inside one momentum fiber. Instead it
identifies the model's direction-indexed current with the canonical charge-like representative.
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

/-- Massive-Dirac velocity as a bounded operator in direction `μ`. -/
noncomputable def velocityOperator
    (direction : Direction2) (v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (velocity direction v)

/-- The bounded current vertex is electron charge times the bounded velocity in either direction. -/
@[simp]
theorem currentOperator_eq_charge_smul_velocityOperator
    (direction : Direction2) (e v : ℝ) :
    currentOperator direction e v = (((-e : ℝ) : ℂ)) • velocityOperator direction v := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (current direction e v) = (((-e : ℝ) : ℂ)) • φ (velocity direction v)
  rw [← canonicalChargeCurrentMatrix_eq_current direction e v]
  unfold canonicalChargeCurrentMatrix
  exact map_smul φ _ _

/-- Canonical symmetrized charge-current linear map in direction `μ`. The generic theorem
`symmetrizedVelocityCurrent_smul_id` reduces this expression to `(-e) v_μ`. -/
noncomputable def canonicalChargeCurrentLinearMap
    (direction : Direction2) (e v : ℝ) : DiracHilbert →ₗ[ℂ] DiracHilbert :=
  QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent DiracHilbert
    (velocityOperator direction v).toLinearMap
    (((-e : ℝ) : ℂ) • LinearMap.id)

/-- The canonical charge-like current from the generic current theory equals the massive-Dirac
bounded current vertex in either in-plane direction. -/
@[simp]
theorem canonicalChargeCurrentLinearMap_eq_currentOperator
    (direction : Direction2) (e v : ℝ) :
    canonicalChargeCurrentLinearMap direction e v = (currentOperator direction e v).toLinearMap := by
  rw [canonicalChargeCurrentLinearMap,
    QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent_smul_id]
  simpa using congrArg
    (fun A : DiracHilbert →L[ℂ] DiracHilbert => A.toLinearMap)
    (currentOperator_eq_charge_smul_velocityOperator direction e v).symm

end

end AnomalousHall.MassiveDirac

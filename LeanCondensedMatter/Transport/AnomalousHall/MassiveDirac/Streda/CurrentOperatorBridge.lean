import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.CurrentBridge

set_option linter.style.header false

/-!
# Bounded-operator realization of the massive-Dirac charge current

This module identifies the direction-indexed bounded current vertex consumed by the Bastin/Středa
stack with the canonical charge-like current `q v` supplied by the generic single-particle current
theory.

The pointwise two-band model still does not instantiate a full real-space localization algebra; the
result is an equality of the chosen canonical current representative with the existing bounded
vertex in either in-plane direction.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

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

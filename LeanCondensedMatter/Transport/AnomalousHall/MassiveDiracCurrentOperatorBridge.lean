import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStreda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracCurrentBridge

set_option linter.style.header false

/-!
# Bounded-operator realization of the massive-Dirac charge current

This module identifies the bounded current vertices already consumed by the Bastin/Středa stack with
the canonical charge-like current `q v` supplied by the generic single-particle current theory.

The pointwise two-band model still does not instantiate a full real-space localization algebra; the
result is an equality of the chosen canonical current representative with the existing bounded
vertices.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Massive-Dirac `x` velocity as a bounded operator on the two-level Hilbert space. -/
noncomputable def velocityXOperator (v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (velocityX v)

/-- Massive-Dirac `y` velocity as a bounded operator on the two-level Hilbert space. -/
noncomputable def velocityYOperator (v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (velocityY v)

/-- The historical bounded `x` current vertex is exactly electron charge times the bounded velocity. -/
@[simp]
theorem currentXOperator_eq_charge_smul_velocityXOperator (e v : ℝ) :
    currentXOperator e v = (((-e : ℝ) : ℂ)) • velocityXOperator v := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (currentX e v) = (((-e : ℝ) : ℂ)) • φ (velocityX v)
  rw [← canonicalChargeCurrentXMatrix_eq_currentX]
  unfold canonicalChargeCurrentXMatrix
  exact map_smul φ _ _

/-- The historical bounded `y` current vertex is exactly electron charge times the bounded velocity. -/
@[simp]
theorem currentYOperator_eq_charge_smul_velocityYOperator (e v : ℝ) :
    currentYOperator e v = (((-e : ℝ) : ℂ)) • velocityYOperator v := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (currentY e v) = (((-e : ℝ) : ℂ)) • φ (velocityY v)
  rw [← canonicalChargeCurrentYMatrix_eq_currentY]
  unfold canonicalChargeCurrentYMatrix
  exact map_smul φ _ _

/-- Canonical symmetrized charge-current linear map in the `x` direction.  The generic theorem
`symmetrizedVelocityCurrent_smul_id` reduces this expression to `(-e) vₓ`. -/
noncomputable def canonicalChargeCurrentXLinearMap (e v : ℝ) :
    DiracHilbert →ₗ[ℂ] DiracHilbert :=
  QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent DiracHilbert
    (velocityXOperator v).toLinearMap
    (((-e : ℝ) : ℂ) • LinearMap.id)

/-- Canonical symmetrized charge-current linear map in the `y` direction. -/
noncomputable def canonicalChargeCurrentYLinearMap (e v : ℝ) :
    DiracHilbert →ₗ[ℂ] DiracHilbert :=
  QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent DiracHilbert
    (velocityYOperator v).toLinearMap
    (((-e : ℝ) : ℂ) • LinearMap.id)

/-- The canonical charge-like `x` current from the generic current theory equals the existing
massive-Dirac bounded current vertex. -/
@[simp]
theorem canonicalChargeCurrentXLinearMap_eq_currentXOperator (e v : ℝ) :
    canonicalChargeCurrentXLinearMap e v = (currentXOperator e v).toLinearMap := by
  rw [canonicalChargeCurrentXLinearMap,
    QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent_smul_id]
  simpa using congrArg
    (fun A : DiracHilbert →L[ℂ] DiracHilbert => A.toLinearMap)
    (currentXOperator_eq_charge_smul_velocityXOperator e v).symm

/-- The canonical charge-like `y` current from the generic current theory equals the existing
massive-Dirac bounded current vertex. -/
@[simp]
theorem canonicalChargeCurrentYLinearMap_eq_currentYOperator (e v : ℝ) :
    canonicalChargeCurrentYLinearMap e v = (currentYOperator e v).toLinearMap := by
  rw [canonicalChargeCurrentYLinearMap,
    QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent_smul_id]
  simpa using congrArg
    (fun A : DiracHilbert →L[ℂ] DiracHilbert => A.toLinearMap)
    (currentYOperator_eq_charge_smul_velocityYOperator e v).symm

end

end AnomalousHall.MassiveDirac

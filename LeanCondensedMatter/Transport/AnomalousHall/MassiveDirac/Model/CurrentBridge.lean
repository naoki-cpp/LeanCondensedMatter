import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Operator
import LeanCondensedMatter.QuantumMechanics.SingleParticle.ChargeLikeCurrent

set_option linter.style.header false

/-!
# Massive-Dirac charge-current representative

The generic charge-like current theorem shows that the canonical corrected/conventional current for
`m = q I` has zero localization correction and reduces to `q v`. This module records the concrete
massive-Dirac realization at both the matrix and bounded-operator levels for either in-plane
direction, together with the canonical in-plane linear-combination boundary reused by longitudinal
and Hall response layers.

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

/-- The bounded velocity is the Dirac velocity scale multiplying the direction Pauli operator. -/
@[simp] theorem velocityOperator_eq_smul_directionPauli
    (direction : Direction2) (v : ℝ) :
    velocityOperator direction v =
      (((v : ℝ) : ℂ)) • matrixOperator (directionPauli direction) := by
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (velocity direction v) =
      (((v : ℝ) : ℂ)) •
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
          (directionPauli direction)
  unfold velocity
  exact map_smul _ _ _

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

/-- Direction-indexed Pauli form of the physical massive-Dirac charge current. -/
@[simp] theorem currentOperator_eq_chargeVelocity_smul_directionPauli
    (direction : Direction2) (e v : ℝ) :
    currentOperator direction e v =
      ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) •
        matrixOperator (directionPauli direction) := by
  rw [currentOperator_eq_charge_smul_velocityOperator,
    velocityOperator_eq_smul_directionPauli, smul_smul]

/-- Dimensionless in-plane Pauli vertex `α σₓ + β σᵧ` as a bounded operator. -/
noncomputable def inPlanePauliVertexOperator
    (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY

@[simp] theorem inPlanePauliVertexOperator_one_zero :
    inPlanePauliVertexOperator 1 0 = matrixOperator sigmaX := by
  simp [inPlanePauliVertexOperator]

@[simp] theorem inPlanePauliVertexOperator_zero_one :
    inPlanePauliVertexOperator 0 1 = matrixOperator sigmaY := by
  simp [inPlanePauliVertexOperator]

/-- Physical in-plane current vertex `α jₓ + β jᵧ`. -/
noncomputable def inPlaneCurrentOperator
    (e v : ℝ) (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  alpha • currentOperator .x e v + beta • currentOperator .y e v

/-- The physical in-plane current is the charge-velocity scale multiplying the corresponding
in-plane Pauli vertex. -/
theorem inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator
    (e v : ℝ) (alpha beta : ℂ) :
    inPlaneCurrentOperator e v alpha beta =
      ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) •
        inPlanePauliVertexOperator alpha beta := by
  rw [inPlaneCurrentOperator,
    currentOperator_eq_chargeVelocity_smul_directionPauli,
    currentOperator_eq_chargeVelocity_smul_directionPauli]
  simp [directionPauli, inPlanePauliVertexOperator, smul_add, smul_smul, mul_comm]

@[simp] theorem inPlaneCurrentOperator_one_zero
    (e v : ℝ) :
    inPlaneCurrentOperator e v 1 0 = currentOperator .x e v := by
  simp [inPlaneCurrentOperator]

@[simp] theorem inPlaneCurrentOperator_zero_one
    (e v : ℝ) :
    inPlaneCurrentOperator e v 0 1 = currentOperator .y e v := by
  simp [inPlaneCurrentOperator]

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

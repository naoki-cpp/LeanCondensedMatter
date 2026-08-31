import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Operator

set_option linter.style.header false

/-!
# Massive-Dirac in-plane current operators

This module owns the small operator-level API built from the model current `j_μ = -e v_μ`: the
bounded velocity, its charge-current relation, and the in-plane linear-combination boundary reused
by longitudinal and Hall response layers.

The canonical charge-like current theorem itself remains upstream. This file does not duplicate it
with model-local wrapper definitions.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

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
  unfold current
  exact map_smul φ _ _

/-- Direction-indexed Pauli form of the physical massive-Dirac charge current. -/
theorem currentOperator_eq_chargeVelocity_smul_directionPauli
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

end

end AnomalousHall.MassiveDirac

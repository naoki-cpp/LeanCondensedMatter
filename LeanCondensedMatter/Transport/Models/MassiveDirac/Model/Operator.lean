import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Bounded-operator realization of the massive-Dirac model

The clean massive-Dirac model is defined first by explicit `2 × 2` matrices. This module owns the
model-level passage from those matrices to bounded operators on the canonical two-level Hilbert
space. It supplies the bounded Hamiltonian, velocity and current vertices, the shared polar Pauli
representation used by rotationally symmetric propagators, their self-adjointness, the in-plane
current-combination API, and the `BoundedFreeSystem` adapter used by generic response theory. Generic
finite-dimensional matrix/operator trace transport lives upstream in `Analysis.Operator.FiniteTrace`.

No Kubo–Bastin or Středa kernel is defined here. Response-specific trace identities and energy
representations remain downstream of this model realization.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory QuantumTheory.LinearResponse QuantumTheory.Transport

/-- Canonical two-level Hilbert space on which the massive-Dirac matrices act. -/
abbrev DiracHilbert := EuclideanSpace ℂ (Fin 2)

/-- A `2 × 2` complex matrix as a bounded operator on the canonical two-level Hilbert space. -/
noncomputable def matrixOperator (M : Matrix2) : DiracHilbert →L[ℂ] DiracHilbert :=
  (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) M

/-- Polar Pauli matrix with a single radial in-plane coefficient. -/
def polarPauliMatrix (a b d : ℂ) (θ : ℝ) : Matrix2 :=
  a • (1 : Matrix2) +
    (((Real.cos θ : ℝ) : ℂ) * b) • sigmaX +
    (((Real.sin θ : ℝ) : ℂ) * b) • sigmaY +
    d • sigmaZ

/-- Bounded-operator realization of `polarPauliMatrix`. -/
noncomputable def polarPauliOperator (a b d : ℂ) (θ : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (polarPauliMatrix a b d θ)

/-- A Cartesian Pauli operator with one common denominator, angle-independent scalar and mass
numerators, and isotropic linear in-plane numerator reduces to `polarPauliOperator` after the polar
substitution `pₓ = p cos θ`, `pᵧ = p sin θ`. -/
theorem commonDenominatorPauliOperator_polar_eq
    (denominator energy mass : ℂ) (v p θ : ℝ) :
    matrixOperator
        ((denominator⁻¹ * energy) • (1 : Matrix2) +
          (denominator⁻¹ * ((v * (p * Real.cos θ) : ℝ) : ℂ)) • sigmaX +
          (denominator⁻¹ * ((v * (p * Real.sin θ) : ℝ) : ℂ)) • sigmaY +
          (denominator⁻¹ * mass) • sigmaZ) =
      polarPauliOperator
        (denominator⁻¹ * energy)
        (denominator⁻¹ * ((v * p : ℝ) : ℂ))
        (denominator⁻¹ * mass) θ := by
  unfold polarPauliOperator
  apply congrArg matrixOperator
  unfold polarPauliMatrix
  push_cast
  module

/-- The clean massive-Dirac Hamiltonian as a bounded operator. -/
noncomputable def hamiltonianOperator (v m px py : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (hamiltonian v m px py)

/-- Massive-Dirac velocity as a bounded operator in direction `μ`. -/
noncomputable def velocityOperator
    (direction : Direction2) (v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (velocity direction v)

/-- Direction-indexed bounded adapter for the massive-Dirac charge-current vertex `j_μ = -e v_μ`. -/
noncomputable def currentOperator
    (direction : Direction2) (e v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (current direction e v)

/-- The bounded current vertex is electron charge times the bounded velocity in either direction. -/
@[simp]
theorem currentOperator_eq_charge_smul_velocityOperator
    (direction : Direction2) (e v : ℝ) :
    currentOperator direction e v = (((-e : ℝ) : ℂ)) • velocityOperator direction v := by
  unfold currentOperator velocityOperator current matrixOperator
  rw [map_smul]

/-- Dimensionless in-plane Pauli vertex `α σₓ + β σᵧ` as a bounded operator. -/
noncomputable def inPlanePauliVertexOperator
    (alpha beta : ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  alpha • matrixOperator sigmaX + beta • matrixOperator sigmaY

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
    currentOperator_eq_charge_smul_velocityOperator,
    currentOperator_eq_charge_smul_velocityOperator]
  unfold velocityOperator velocity inPlanePauliVertexOperator matrixOperator
  rw [map_smul, map_smul]
  simp only [directionPauli]
  push_cast
  module

/-- The explicit massive-Dirac Hamiltonian matrix is Hermitian. -/
theorem hamiltonian_isHermitian (v m px py : ℝ) :
    (hamiltonian v m px py).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, sigmaX, sigmaY, sigmaZ]

/-- The charge-current matrix is Hermitian in either in-plane direction. -/
theorem current_isHermitian (direction : Direction2) (e v : ℝ) :
    (current direction e v).IsHermitian := by
  cases direction <;>
    apply Matrix.IsHermitian.ext <;>
    intro i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [current, velocity, directionPauli, sigmaX, sigmaY]

/-- Transporting the Hermitian Hamiltonian through `Matrix.toEuclideanCLM` gives a self-adjoint
bounded operator, as required by the generic free-system API. -/
theorem hamiltonianOperator_isSelfAdjoint (v m px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator v m px py) := by
  simpa [hamiltonianOperator, matrixOperator] using
    (hamiltonian_isHermitian v m px py).isSelfAdjoint.map
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The direction-indexed current operator is self-adjoint. -/
theorem currentOperator_isSelfAdjoint (direction : Direction2) (e v : ℝ) :
    IsSelfAdjoint (currentOperator direction e v) := by
  simpa [currentOperator, matrixOperator] using
    (current_isHermitian direction e v).isSelfAdjoint.map
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The clean massive-Dirac model as the bounded free system consumed by generic response layers.
The currents remain supplied separately because `BoundedFreeSystem` intentionally stores only
Hamiltonian dynamics and `ℏ`. -/
noncomputable def boundedFreeSystem (hbar v m px py : ℝ) (hhbar : 0 < hbar) :
    BoundedFreeSystem DiracHilbert where
  hamiltonian := ⟨hamiltonianOperator v m px py, hamiltonianOperator_isSelfAdjoint v m px py⟩
  hbar := hbar
  hbar_pos := hhbar

end

end QuantumTheory.Transport.Models.MassiveDirac

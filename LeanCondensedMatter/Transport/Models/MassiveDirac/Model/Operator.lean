import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

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
    (direction : Fin 2) (v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (velocity direction v)

/-- Direction-indexed bounded adapter for the massive-Dirac charge-current vertex `j_μ = -e v_μ`. -/
noncomputable def currentOperator
    (direction : Fin 2) (e v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (current direction e v)

/-- The bounded current vertex is electron charge times the bounded velocity in either direction. -/
@[simp]
theorem currentOperator_eq_charge_smul_velocityOperator
    (direction : Fin 2) (e v : ℝ) :
    currentOperator direction e v = (((-e : ℝ) : ℂ)) • velocityOperator direction v := by
  unfold currentOperator velocityOperator current matrixOperator
  rw [map_smul]

/-- Dimensionless in-plane Pauli vertex with direction-indexed coefficients. -/
noncomputable def inPlanePauliVertexOperator
    (coefficients : Fin 2 → ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  coefficients 0 • matrixOperator sigmaX + coefficients 1 • matrixOperator sigmaY

/-- Canonical complex-linear embedding of in-plane coefficients into the Pauli-operator subspace. -/
noncomputable def inPlanePauliVertexCLM :
    (Fin 2 → ℂ) →L[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := by
  let linearMap : (Fin 2 → ℂ) →ₗ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) :=
    { toFun := inPlanePauliVertexOperator
      map_add' := by
        intro left right
        simp [inPlanePauliVertexOperator, add_smul]
        module
      map_smul' := by
        intro scalar coefficients
        simp [inPlanePauliVertexOperator, smul_smul]
        }
  exact ⟨linearMap, linearMap.continuous_of_finiteDimensional⟩

@[simp]
theorem inPlanePauliVertexCLM_apply (coefficients : Fin 2 → ℂ) :
    inPlanePauliVertexCLM coefficients = inPlanePauliVertexOperator coefficients := by
  rfl

/-- The in-plane Pauli realization is faithful: its two coefficients are recovered uniquely from
the represented bounded operator. -/
theorem inPlanePauliVertexCLM_injective :
    Function.Injective inPlanePauliVertexCLM := by
  intro left right h
  have hoperator :
      inPlanePauliVertexOperator left = inPlanePauliVertexOperator right := by
    simpa only [inPlanePauliVertexCLM_apply] using h
  have hmatrix :
      left 0 • sigmaX + left 1 • sigmaY =
        right 0 • sigmaX + right 1 • sigmaY := by
    have hmatrix' := congrArg
      (fun A : DiracHilbert →L[ℂ] DiracHilbert =>
        (Matrix.toEuclideanCLM :
          Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).symm A)
      hoperator
    simpa [inPlanePauliVertexOperator, matrixOperator, map_add, map_smul] using hmatrix'
  have hxy : LinearIndependent ℂ ![sigmaX, sigmaY] := by
    simpa [directionPauli, inPlanePauliAxis, InternalSpace.pauliBasis] using
      directionPauli_linearIndependent
  have hcoeff := hxy.eq_of_pair hmatrix
  funext direction
  fin_cases direction
  · exact hcoeff.1
  · exact hcoeff.2

/-- Physical in-plane current vertex with direction-indexed coefficients. -/
noncomputable def inPlaneCurrentOperator
    (e v : ℝ) (coefficients : Fin 2 → ℂ) : DiracHilbert →L[ℂ] DiracHilbert :=
  coefficients 0 • currentOperator 0 e v + coefficients 1 • currentOperator 1 e v

/-- The physical in-plane current is the charge-velocity scale multiplying the corresponding
in-plane Pauli vertex. -/
theorem inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator
    (e v : ℝ) (coefficients : Fin 2 → ℂ) :
    inPlaneCurrentOperator e v coefficients =
      ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) • inPlanePauliVertexOperator coefficients := by
  rw [inPlaneCurrentOperator,
    currentOperator_eq_charge_smul_velocityOperator,
    currentOperator_eq_charge_smul_velocityOperator]
  unfold velocityOperator velocity inPlanePauliVertexOperator matrixOperator
  rw [map_smul, map_smul]
  simp [directionPauli, inPlanePauliAxis, InternalSpace.pauliBasis]
  module

/-- The explicit massive-Dirac Hamiltonian matrix is Hermitian. -/
theorem hamiltonian_isHermitian (v m px py : ℝ) :
    (hamiltonian v m px py).IsHermitian := by
  rw [hamiltonian_eq_pauliCombination]
  let u : PauliAxis → ℝ
    | .x => v * px
    | .y => v * py
    | .z => m
  have hcoefficients :
      diracPauliCoefficients v m px py = fun axis => (u axis : ℂ) := by
    funext axis
    cases axis <;> rfl
  rw [hcoefficients]
  exact InternalSpace.pauliCombination_ofReal_isHermitian u

private theorem directionPauli_isHermitian (direction : Fin 2) :
    (directionPauli direction).IsHermitian := by
  exact InternalSpace.pauliBasis_isHermitian (inPlanePauliAxis direction)

/-- The velocity matrix is Hermitian in either in-plane direction. -/
theorem velocity_isHermitian (direction : Fin 2) (v : ℝ) :
    (velocity direction v).IsHermitian := by
  unfold velocity
  exact (directionPauli_isHermitian direction).smul (by simp [isSelfAdjoint_iff])

/-- The charge-current matrix is Hermitian in either in-plane direction. -/
theorem current_isHermitian (direction : Fin 2) (e v : ℝ) :
    (current direction e v).IsHermitian := by
  unfold current velocity
  exact
    ((directionPauli_isHermitian direction).smul (by simp [isSelfAdjoint_iff])).smul
      (by simp [isSelfAdjoint_iff])

/-- Transporting the Hermitian Hamiltonian through `Matrix.toEuclideanCLM` gives a self-adjoint
bounded operator, as required by the generic free-system API. -/
theorem hamiltonianOperator_isSelfAdjoint (v m px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator v m px py) := by
  simpa [hamiltonianOperator, matrixOperator] using
    (hamiltonian_isHermitian v m px py).isSelfAdjoint.map
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The direction-indexed velocity operator is self-adjoint. -/
theorem velocityOperator_isSelfAdjoint (direction : Fin 2) (v : ℝ) :
    IsSelfAdjoint (velocityOperator direction v) := by
  simpa [velocityOperator, matrixOperator] using
    (velocity_isHermitian direction v).isSelfAdjoint.map
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The direction-indexed current operator is self-adjoint. -/
theorem currentOperator_isSelfAdjoint (direction : Fin 2) (e v : ℝ) :
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

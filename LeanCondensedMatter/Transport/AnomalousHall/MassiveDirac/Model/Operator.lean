import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic
import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Bounded-operator realization of the massive-Dirac model

The clean massive-Dirac model is defined first by explicit `2 × 2` matrices. This module owns the
model-level passage from those matrices to bounded operators on the canonical two-level Hilbert
space. It supplies the bounded Hamiltonian and current vertices, their self-adjointness, the
`BoundedFreeSystem` adapter used by generic response theory, and the exact matrix/operator trace
bridge.

No Kubo–Bastin or Středa kernel is defined here. Response-specific trace identities and energy
representations remain downstream of this model realization.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory QuantumTheory.LinearResponse QuantumTheory.Transport

/-- Canonical two-level Hilbert space on which the massive-Dirac matrices act. -/
abbrev DiracHilbert := EuclideanSpace ℂ (Fin 2)

/-- A `2 × 2` complex matrix as a bounded operator on the canonical two-level Hilbert space. -/
noncomputable def matrixOperator (M : Matrix2) : DiracHilbert →L[ℂ] DiracHilbert :=
  (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) M

/-- The ordinary matrix trace agrees with the finite-dimensional operator trace after transporting
through the canonical Euclidean-space matrix/operator equivalence. -/
theorem finiteDimensionalOperatorTrace_matrixOperator (M : Matrix2) :
    finiteDimensionalOperatorTrace (matrixOperator M) = Matrix.trace M := by
  rw [finiteDimensionalOperatorTrace_apply]
  have hcoe :
      ((matrixOperator M : DiracHilbert →L[ℂ] DiracHilbert) :
        DiracHilbert →ₗ[ℂ] DiracHilbert) = Matrix.toEuclideanLin M := by
    simpa [matrixOperator] using Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M
  rw [hcoe, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq M (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis

/-- The clean massive-Dirac Hamiltonian as a bounded operator. -/
noncomputable def hamiltonianOperator (v m px py : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (hamiltonian v m px py)

/-- Direction-indexed bounded adapter for the massive-Dirac charge-current vertex `j_μ = -e v_μ`. -/
noncomputable def currentOperator
    (direction : Direction2) (e v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (current direction e v)

/-- Canonical bounded-operator form of the massive-Dirac `x` charge current. -/
@[simp] theorem currentOperator_x_eq_pauli (e v : ℝ) :
    currentOperator .x e v =
      (((-e * v : ℝ) : ℂ)) • matrixOperator sigmaX := by
  have hcurrent :
      current .x e v = (((-e * v : ℝ) : ℂ)) • sigmaX := by
    simp [current, velocity, directionPauli, smul_smul]
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (current .x e v) =
      (((-e * v : ℝ) : ℂ)) •
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaX
  rw [hcurrent, map_smul]

/-- Canonical bounded-operator form of the massive-Dirac `y` charge current. -/
@[simp] theorem currentOperator_y_eq_pauli (e v : ℝ) :
    currentOperator .y e v =
      (((-e * v : ℝ) : ℂ)) • matrixOperator sigmaY := by
  have hcurrent :
      current .y e v = (((-e * v : ℝ) : ℂ)) • sigmaY := by
    simp [current, velocity, directionPauli, smul_smul]
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (current .y e v) =
      (((-e * v : ℝ) : ℂ)) •
        (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaY
  rw [hcurrent, map_smul]

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
  change IsSelfAdjoint
    ((Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
      (hamiltonian v m px py))
  exact (hamiltonian_isHermitian v m px py).isSelfAdjoint.map
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The direction-indexed current operator is self-adjoint. -/
theorem currentOperator_isSelfAdjoint (direction : Direction2) (e v : ℝ) :
    IsSelfAdjoint (currentOperator direction e v) := by
  change IsSelfAdjoint
    ((Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
      (current direction e v))
  exact (current_isHermitian direction e v).isSelfAdjoint.map
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The clean massive-Dirac model as the bounded free system consumed by generic response layers.
The currents remain supplied separately because `BoundedFreeSystem` intentionally stores only
Hamiltonian dynamics and `ℏ`. -/
noncomputable def boundedFreeSystem (hbar v m px py : ℝ) (hhbar : 0 < hbar) :
    BoundedFreeSystem DiracHilbert where
  hamiltonian := ⟨hamiltonianOperator v m px py, hamiltonianOperator_isSelfAdjoint v m px py⟩
  hbar := hbar
  hbar_pos := hhbar

@[simp]
theorem boundedFreeSystem_hamiltonian (hbar v m px py : ℝ) (hhbar : 0 < hbar) :
    (boundedFreeSystem hbar v m px py hhbar).hamiltonian.1 =
      hamiltonianOperator v m px py :=
  rfl

@[simp]
theorem boundedFreeSystem_hbar (hbar v m px py : ℝ) (hhbar : 0 < hbar) :
    (boundedFreeSystem hbar v m px py hhbar).hbar = hbar :=
  rfl

end

end AnomalousHall.MassiveDirac

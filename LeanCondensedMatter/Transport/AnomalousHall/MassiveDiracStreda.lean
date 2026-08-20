import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsicConductivity
import LeanCondensedMatter.Transport.StredaTraceKernel
import LeanCondensedMatter.Transport.LinearResponse
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Massive-Dirac bridge to the finite Bastin/Středa operator API

The clean AHE development starts from explicit `2 × 2` matrices, while the generic transport stack
uses bounded operators on Hilbert spaces.  This file provides the concrete bridge between those two
representations without introducing an independent response formalism.

`Matrix.toEuclideanCLM` identifies a complex `2 × 2` matrix with a bounded operator on the canonical
two-level Euclidean Hilbert space.  The massive-Dirac Hamiltonian is proved Hermitian before being
bundled as a `BoundedFreeSystem`; the concrete current matrices are transported by the same
star-algebra equivalence.  These bounded current vertices remain the adapter boundary consumed by
the existing Bastin/Středa stack.  Their identification with the canonical charge-like `q v`
representative at `q = -e` is proved downstream in `MassiveDiracCurrentOperatorBridge`, so this file
does not make the concrete matrices a separate foundational current convention.

The ordinary matrix trace is also identified with the finite-dimensional operator trace used by the
generic transport layer.  The existing pointwise Bastin/Středa trace identity can then be
instantiated directly for the massive-Dirac Hamiltonian and its canonical-derived concrete current
vertices.

This file does not yet choose an eigenvector gauge, evaluate the resolvent spectral sum, remove the
finite broadening, or identify the generic transport normalization with the continuum Berry result.
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

/-- Concrete bounded adapter for the canonical-derived charge-current vertex `jₓ = -e v σₓ`.
`MassiveDiracCurrentOperatorBridge` proves that this equals the generic charge-like representative. -/
noncomputable def currentXOperator (e v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (currentX e v)

/-- Concrete bounded adapter for the canonical-derived charge-current vertex `jᵧ = -e v σᵧ`;
its equality with the generic `q v` representative is proved in `MassiveDiracCurrentOperatorBridge`. -/
noncomputable def currentYOperator (e v : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (currentY e v)

/-- The explicit massive-Dirac Hamiltonian matrix is Hermitian. -/
theorem hamiltonian_isHermitian (v m px py : ℝ) :
    (hamiltonian v m px py).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, sigmaX, sigmaY, sigmaZ]

/-- The `x` charge-current matrix is Hermitian for real charge magnitude and velocity. -/
theorem currentX_isHermitian (e v : ℝ) :
    (currentX e v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [currentX, sigmaX]

/-- The `y` charge-current matrix is Hermitian for real charge magnitude and velocity. -/
theorem currentY_isHermitian (e v : ℝ) :
    (currentY e v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [currentY, sigmaY]

/-- Transporting the Hermitian Hamiltonian through `Matrix.toEuclideanCLM` gives a self-adjoint
bounded operator, as required by the generic free-system API. -/
theorem hamiltonianOperator_isSelfAdjoint (v m px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator v m px py) := by
  change IsSelfAdjoint
    ((Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
      (hamiltonian v m px py))
  exact (hamiltonian_isHermitian v m px py).isSelfAdjoint.map
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The concrete `x` current operator is self-adjoint. -/
theorem currentXOperator_isSelfAdjoint (e v : ℝ) :
    IsSelfAdjoint (currentXOperator e v) := by
  change IsSelfAdjoint
    ((Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
      (currentX e v))
  exact (currentX_isHermitian e v).isSelfAdjoint.map
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The concrete `y` current operator is self-adjoint. -/
theorem currentYOperator_isSelfAdjoint (e v : ℝ) :
    IsSelfAdjoint (currentYOperator e v) := by
  change IsSelfAdjoint
    ((Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
      (currentY e v))
  exact (currentY_isHermitian e v).isSelfAdjoint.map
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))

/-- The clean massive-Dirac model as the bounded free system consumed by the generic response and
Středa layers.  The currents remain supplied separately because `BoundedFreeSystem` intentionally
stores only Hamiltonian dynamics and `ℏ`. -/
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

/-- Pointwise finite-broadening Bastin/Středa identity specialized to the actual massive-Dirac
Hamiltonian and canonical-derived concrete charge-current vertices. -/
theorem regularizedBastinTraceIntegrand_eq_streda
    (e v m px py energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v) energy broadening =
      regularizedStredaSurfacePrimitiveTraceDerivative
          (hamiltonianOperator v m px py)
          (currentXOperator e v) (currentYOperator e v) energy broadening +
        regularizedStredaResidualSeaTraceKernel
          (hamiltonianOperator v m px py)
          (currentXOperator e v) (currentYOperator e v) energy broadening :=
  QuantumTheory.Transport.regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea
    (hamiltonianOperator v m px py)
    (currentXOperator e v) (currentYOperator e v) energy broadening

end

end AnomalousHall.MassiveDirac

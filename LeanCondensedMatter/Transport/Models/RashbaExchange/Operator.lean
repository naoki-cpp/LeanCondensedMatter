import LeanCondensedMatter.Transport.Models.RashbaExchange.Model
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Bounded-operator realization of the Rashba-exchange model

This file is the model-to-response boundary. Matrices remain the primary model representation;
generic finite-dimensional Středa response theory consumes their bounded-operator realization.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport

/-- Two-component Hilbert space used by the Rashba-exchange benchmark. -/
abbrev RashbaHilbert := EuclideanSpace ℂ (Fin 2)

/-- Canonical bounded-operator realization of a two-by-two Pauli matrix. -/
noncomputable def matrixOperator (M : InternalSpace.PauliMatrix) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  (Matrix.toEuclideanCLM :
    InternalSpace.PauliMatrix ≃⋆ₐ[ℂ] (RashbaHilbert →L[ℂ] RashbaHilbert)) M

/-- Bounded-operator realization of the model Hamiltonian. -/
noncomputable def hamiltonianOperator (params : Parameters) (px py : ℝ) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  matrixOperator (hamiltonian params px py)

/-- Bounded-operator realization of the matrix velocity operator. -/
noncomputable def velocityBoundedOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  matrixOperator (velocityOperator params direction px py)

/-- Bounded charge-current operator consumed by response kernels. -/
noncomputable def currentBoundedOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  matrixOperator (currentOperator params direction px py)

@[simp] theorem currentBoundedOperator_eq_charge_smul_velocity
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    currentBoundedOperator params direction px py =
      (((params.signedCharge : ℝ) : ℂ)) •
        velocityBoundedOperator params direction px py := by
  unfold currentBoundedOperator velocityBoundedOperator currentOperator matrixOperator
  rw [map_smul]

/-- Canonical retarded or advanced Green resolvent at the chemical potential. -/
noncomputable def greenOperator
    (side : SpectralSide) (params : Parameters) (px py : ℝ) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  match side with
  | .retarded =>
      retardedResolvent (hamiltonianOperator params px py)
        params.chemicalPotential params.broadening
  | .advanced =>
      advancedResolvent (hamiltonianOperator params px py)
        params.chemicalPotential params.broadening

end
end QuantumTheory.Transport.Models.RashbaExchange

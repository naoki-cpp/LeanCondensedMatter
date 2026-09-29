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

abbrev RashbaHilbert := EuclideanSpace ℂ (Fin 2)

noncomputable def matrixOperator (M : Matrix2) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  (Matrix.toEuclideanCLM :
    Matrix2 ≃⋆ₐ[ℂ] (RashbaHilbert →L[ℂ] RashbaHilbert)) M

noncomputable def hamiltonianOperator (params : Parameters) (px py : ℝ) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  matrixOperator (hamiltonian params px py)

noncomputable def velocityBoundedOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    RashbaHilbert →L[ℂ] RashbaHilbert :=
  matrixOperator (velocityOperator params direction px py)

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

import LeanCondensedMatter.Transport.Models.RashbaExchange.Model

import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.Analysis.InnerProductSpace.PiL2
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

/-- Canonical bounded-operator realization of a two-by-two Pauli matrix. -/
noncomputable def matrixOperator (M : InternalSpace.PauliMatrix) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanCLM :
    InternalSpace.PauliMatrix ≃⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) M

/-- Bounded-operator realization of the model Hamiltonian. -/
noncomputable def hamiltonianOperator (params : Parameters) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (hamiltonian params px py)

/-- Bounded-operator realization of the matrix velocity operator. -/
noncomputable def velocityBoundedOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (velocityOperator params direction px py)

/-- Bounded charge-current operator consumed by response kernels. -/
noncomputable def currentBoundedOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (currentOperator params direction px py)

@[simp] theorem currentBoundedOperator_eq_charge_smul_velocity
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    currentBoundedOperator params direction px py =
      (((params.signedCharge : ℝ) : ℂ)) •
        velocityBoundedOperator params direction px py := by
  unfold currentBoundedOperator velocityBoundedOperator currentOperator matrixOperator
  rw [map_smul]

/-- The explicit Rashba-exchange Hamiltonian matrix is Hermitian for real model parameters. -/
theorem hamiltonian_isHermitian (params : Parameters) (px py : ℝ) :
    (hamiltonian params px py).IsHermitian := by
  let u : InternalSpace.PauliAxis → ℝ
    | .x => params.rashbaVelocity * py
    | .y => -params.rashbaVelocity * px
    | .z => params.exchangeSplitting
  have hcoeff :
      rashbaPauliCoefficients params px py = fun axis => (u axis : ℂ) := by
    funext axis
    cases axis <;> rfl
  have hscalar :
      (((kineticEnergy params px py : ℝ) : ℂ) •
        (1 : InternalSpace.PauliMatrix)).IsHermitian := by
    simp [Matrix.IsHermitian]
  have hpauli :
      (InternalSpace.pauliCombination (rashbaPauliCoefficients params px py)).IsHermitian := by
    rw [hcoeff]
    exact InternalSpace.pauliCombination_ofReal_isHermitian u
  simpa [hamiltonian] using hscalar.add hpauli

/-- The bounded Rashba-exchange Hamiltonian is self-adjoint, providing the analytic provenance
required by the generic finite-broadening Středa/Bastin layer. -/
theorem hamiltonianOperator_isSelfAdjoint (params : Parameters) (px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator params px py) := by
  simpa [hamiltonianOperator, matrixOperator] using
    (hamiltonian_isHermitian params px py).isSelfAdjoint.map
      (Matrix.toEuclideanCLM :
        InternalSpace.PauliMatrix ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))

/-- Canonical retarded or advanced Green resolvent at the chemical potential. -/
noncomputable def greenOperator
    (side : SpectralSide) (params : Parameters) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  match side with
  | .retarded =>
      retardedResolvent (hamiltonianOperator params px py)
        params.chemicalPotential params.broadening
  | .advanced =>
      advancedResolvent (hamiltonianOperator params px py)
        params.chemicalPotential params.broadening

end
end QuantumTheory.Transport.Models.RashbaExchange

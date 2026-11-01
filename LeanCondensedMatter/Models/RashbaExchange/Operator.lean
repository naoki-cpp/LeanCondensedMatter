import LeanCondensedMatter.Models.RashbaExchange.Model
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Bounded-operator realization of the Rashba-exchange model

The clean Rashba Hamiltonian and velocity matrices are lifted to bounded operators using
only `HamiltonianParameters`. Their self-adjointness is proved here. Charge-current matrices
and their bounded realizations are owned by `Current`; finite-broadening Green resolvents
are defined in the separate `Green` module.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

/-- Canonical bounded-operator realization of a two-by-two Pauli matrix. -/
noncomputable def matrixOperator (M : InternalSpace.PauliMatrix) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanCLM :
    InternalSpace.PauliMatrix ≃⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) M

/-- Bounded-operator realization of the model Hamiltonian. -/
noncomputable def hamiltonianOperator (params : HamiltonianParameters) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (hamiltonian params px py)

/-- Bounded-operator realization of the matrix velocity operator. -/
noncomputable def velocityBoundedOperator
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (velocityOperator params direction px py)

/-- The explicit Rashba-exchange Hamiltonian matrix is Hermitian for real model parameters. -/
theorem hamiltonian_isHermitian (params : HamiltonianParameters) (px py : ℝ) :
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
theorem hamiltonianOperator_isSelfAdjoint (params : HamiltonianParameters) (px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator params px py) := by
  simpa [hamiltonianOperator, matrixOperator] using
    (hamiltonian_isHermitian params px py).isSelfAdjoint.map
      (Matrix.toEuclideanCLM :
        InternalSpace.PauliMatrix ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))


end
end QuantumTheory.Models.RashbaExchange

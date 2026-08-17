import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation

/-!
# Energy expectation values

The generic real-valued expectation of a bounded observable is owned by
`DensityOperator.observableExpectation`. This module retains the thermodynamic name
`energyExpValue` as the Hamiltonian-facing specialization used by the Gibbs and free-energy APIs.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real expectation value of a bounded Hamiltonian in a density state. This is the
thermodynamic specialization of `DensityOperator.observableExpectation`. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  ρ.observableExpectation Hop

end QuantumTheory

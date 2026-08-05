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

/-- The spectral series used by the energy expectation is summable. -/
theorem summable_energyExpValue_term (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (Hop.1 (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) :=
  ρ.summable_observableExpectation_term Hop

/-- The real expectation value of a bounded Hamiltonian in a density state. This is the
thermodynamic specialization of `DensityOperator.observableExpectation`. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  ρ.observableExpectation Hop

/-- Energy expectation is definitionally the generic real observable expectation. -/
@[simp]
theorem energyExpValue_eq_observableExpectation
    (ρ : DensityOperator H) (Hop : Observable H) :
    energyExpValue ρ Hop = ρ.observableExpectation Hop :=
  rfl

end QuantumTheory

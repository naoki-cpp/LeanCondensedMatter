import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation

/-!
# Energy expectation values

The real energy expectation is the real part of the canonical complex expectation functional.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral series used by the energy expectation is summable. -/
theorem summable_energyExpValue_term (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (Hop.1 (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) :=
  ρ.summable_expectation_term Hop.1

/-- The expectation value of a bounded observable in a density state. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  (ρ.expectation Hop.1).re

end QuantumTheory

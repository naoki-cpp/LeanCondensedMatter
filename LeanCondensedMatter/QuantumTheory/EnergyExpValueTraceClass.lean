import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationTraceClass

/-!
# Energy expectation value via trace-class density operators

The real energy expectation is the real part of the canonical complex expectation functional on
bounded operators. The generic spectral summability, linearity, normalization, and norm bound are
owned by `DensityOperator.expectation`.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral series used by the energy expectation is summable. This is a derived real-observable
specialization of `DensityOperator.summable_expectation_term`, not a separate implementation. -/
theorem summable_energyExpValue_term (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (Hop.1 (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) :=
  ρ.summable_expectation_term Hop.1

/-- The expectation value of a bounded observable in a trace-class density state. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  (ρ.expectation Hop.1).re

end QuantumTheory.TraceClass

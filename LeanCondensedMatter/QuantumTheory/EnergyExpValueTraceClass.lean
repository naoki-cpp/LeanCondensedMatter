import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationTraceClass

/-!
# Energy expectation value via trace-class density operators

The real energy expectation is the real part of the canonical complex expectation functional on
bounded operators.  The generic spectral summability, linearity, normalization, and norm bound are
owned by `DensityOperator.expectation`.
-/

namespace QuantumTheory.TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation value of a bounded observable in a trace-class density state. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  (ρ.expectation Hop.1).re

end QuantumTheory.TraceClass

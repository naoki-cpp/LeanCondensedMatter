import LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteLehmannTable

set_option linter.style.header false

/-!
# Public finite-response evaluation boundary

This module packages the theorem-level scalar evaluation API introduced by
`FiniteLehmannTable`.  A later charge, spin, or other finite response calculation may supply only

```text
Eₙ, pₙ, Aₘₙ, Bₘₙ, ℏ, ω, η
```

and evaluate the already-proved finite Lehmann formula without rebuilding the Kubo derivation.
`FiniteResponseProblem` merely bundles those scalar inputs with the physical frequency parameters;
its `value` is exactly `finiteLehmannTableResponse`.

The constructor from `PurePointLehmannData` records the bridge back to the operator-level theorem.
Thus callers may either construct a scalar table directly, or derive one from proved spectral data,
while using the same evaluator.

This is the exact/theorem-level boundary: data remain in `ℝ` and `ℂ`, and this module introduces no
`Float`, numerical diagonalization, tolerance, or approximation semantics.  Any future numerical
backend should live downstream and make its approximation/error model explicit.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Complete scalar input for one exact finite fixed-rate linear-response evaluation. -/
structure FiniteResponseProblem (ι : Type*) where
  /-- Reduced Planck constant used by the finite Lehmann kernel. -/
  hbar : ℝ
  /-- Observation/driving angular frequency. -/
  omega : ℝ
  /-- Positive-rate/broadening parameter retained explicitly by the evaluator. -/
  eta : ℝ
  /-- Finite spectral energies, probabilities, and observable matrix elements. -/
  table : FiniteLehmannTable ι

/-- Evaluate a bundled finite response problem with the existing scalar Lehmann evaluator. -/
noncomputable def FiniteResponseProblem.value
    {ι : Type*} [Fintype ι] (problem : FiniteResponseProblem ι) : ℂ :=
  finiteLehmannTableResponse problem.hbar problem.omega problem.eta problem.table

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Package a proved finite pure-point operator problem into the public scalar evaluation input. -/
noncomputable def finiteResponseProblemOfPurePoint
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : FiniteResponseProblem ι where
  hbar := system.hbar
  omega := omega
  eta := eta
  table := finiteLehmannTableOfPurePoint system data A B

/-- Evaluating the packaged scalar problem obtained from pure-point data is exactly the existing
operator-level finite Lehmann series. -/
theorem finiteResponseProblemOfPurePoint_value
    [Fintype ι]
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    (finiteResponseProblemOfPurePoint system data A B omega eta).value =
      purePointLehmannSeries system data A B omega eta := by
  simpa [FiniteResponseProblem.value, finiteResponseProblemOfPurePoint] using
    finiteLehmannTableResponse_ofPurePoint system data A B omega eta

end
end LinearResponse
end QuantumTheory

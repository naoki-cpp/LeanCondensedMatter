import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.RetardedSusceptibility

set_option linter.style.header false

/-!
# Response channels for bounded observables

The generic causal Kubo API keeps the measured observable and source coupling independent, while
`ObservableVariation` keeps the first-order source dependence of the measured observable explicit.
This module packages those three pieces as neutral response-channel data:

```text
measured
source
observableVariation
```

The associated scalar response is the causal retarded convolution plus the explicit contact term.
No transport, current-density, conductivity, Kubo–Bastin, or Středa semantics are imposed here.
Those remain downstream specializations.

Channel evaluation takes a one-parameter unitary group and an explicit `hbar`, rather than a
bounded Hamiltonian. The contact expectation only uses the group. This evaluation does not itself
derive a perturbative response or assert integrability; those hypotheses remain with the callers.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Neutral data specifying one bounded linear-response channel.

`measured` is the source-independent zeroth-order measured observable, `source` is the operator
coupled to the scalar source, and `observableVariation` is the first-order variation of the
measured observable itself.  The latter is kept explicit so contact terms are not silently dropped
when generalized currents depend on the external source. -/
structure ResponseChannel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Zeroth-order measured observable. -/
  measured : H →L[ℂ] H
  /-- Operator coupled to the scalar source. -/
  source : H →L[ℂ] H
  /-- Actual coefficient of the affine measured-observable variation at observation time.
  Any source-profile factor prescribed for that coefficient is supplied by the caller. -/
  observableVariation : H →L[ℂ] H

namespace ResponseChannel

/-- A response channel whose measured observable has no explicit first-order source variation. -/
noncomputable def fixed
    (measured source : H →L[ℂ] H) : ResponseChannel H where
  measured := measured
  source := source
  observableVariation := 0

/-- Retarded kernel associated with the measured/source pair of a response channel. -/
noncomputable def retardedKernel
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (t s : ℝ) : ℂ :=
  retardedSusceptibility U hbar expectation channel.measured channel.source t s

/-- Explicit contact contribution carried by a response channel at the observation time. -/
noncomputable def contactExpectation
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (expectation : NormalizedExpectation H)
    (t : ℝ) : ℂ :=
  expectation (heisenbergEvolution U t channel.observableVariation)

/-- Causal scalar response of a channel to a real source profile.

The first term is the ordinary retarded Kubo response and the second is the explicit observable
variation/contact contribution. The profile is not applied again to the supplied variation. -/
noncomputable def causalResponse
    (channel : ResponseChannel H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (∫ s in (0 : ℝ)..t, (f s : ℂ) * channel.retardedKernel U hbar expectation t s) +
    channel.contactExpectation U expectation t

@[simp]
theorem fixed_contactExpectation
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (t : ℝ) :
    (fixed measured source).contactExpectation U expectation t = 0 := by
  simp [contactExpectation, fixed, heisenbergEvolution_apply]

/-- A fixed-observable channel reduces to the ordinary causal retarded convolution. -/
theorem fixed_causalResponse_eq
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ) :
    (fixed measured source).causalResponse U hbar expectation f t =
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) * retardedSusceptibility U hbar expectation measured source t s := by
  simp [causalResponse, retardedKernel, contactExpectation, fixed,
    heisenbergEvolution_apply]

end ResponseChannel

end
end LinearResponse
end QuantumTheory

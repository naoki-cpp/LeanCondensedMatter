import LeanCondensedMatter.QuantumTheory.LinearResponse.ObservableVariation

set_option linter.style.header false

/-!
# Response channels for bounded linear response

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
  /-- First-order source variation of the measured observable. -/
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
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (t s : ℝ) : ℂ :=
  retardedSusceptibility system expectation channel.measured channel.source t s

/-- Explicit contact contribution carried by a response channel at the observation time. -/
noncomputable def contactExpectation
    (channel : ResponseChannel H)
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (t : ℝ) : ℂ :=
  expectation (heisenbergEvolution system channel.observableVariation t)

/-- Causal scalar response of a channel to a real source profile.

The first term is the ordinary retarded Kubo response and the second is the explicit observable
variation/contact contribution. -/
noncomputable def causalResponse
    (channel : ResponseChannel H)
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (∫ s in (0 : ℝ)..t, (f s : ℂ) * channel.retardedKernel system expectation t s) +
    channel.contactExpectation system expectation t

@[simp]
theorem fixed_contactExpectation
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (t : ℝ) :
    (fixed measured source).contactExpectation system expectation t = 0 := by
  simp [contactExpectation, fixed, heisenbergEvolution]

/-- A fixed-observable channel reduces to the ordinary causal retarded convolution. -/
theorem fixed_causalResponse_eq
    (system : BoundedFreeSystem H) (expectation : NormalizedExpectation H)
    (measured source : H →L[ℂ] H) (f : ℝ → ℝ) (t : ℝ) :
    (fixed measured source).causalResponse system expectation f t =
      ∫ s in (0 : ℝ)..t,
        (f s : ℂ) * retardedSusceptibility system expectation measured source t s := by
  simp [causalResponse, retardedKernel, contactExpectation, fixed, heisenbergEvolution]

end ResponseChannel

end
end LinearResponse
end QuantumTheory

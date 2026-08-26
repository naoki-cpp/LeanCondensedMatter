import LeanCondensedMatter.Transport.KuboBastin.Finite
import LeanCondensedMatter.Transport.Streda.Integration

set_option linter.style.header false

/-!
# Static generalized Kubo–Bastin response and Středa boundary

The generalized finite Kubo–Bastin layer keeps three response-channel inputs independent:

```text
measured A₀
source B
observable variation A₁.
```

At zero driving frequency the finite spectral Bastin response has two conceptually distinct pieces:

```text
vertex response(A₀,B) + ⟨A₁⟩.
```

Only the two-vertex spectral response is fed into `RegularizedStredaRepresentation`. The explicit
observable-variation expectation remains outside the surface/sea integration-by-parts split.

This boundary is statistics-independent and does not require finite dimensionality of the Hilbert
space. Ordinary finite-dimensional traces enter only in the canonical static Bastin trace layer
under `Transport.Streda.TraceKernel` and `Transport.Streda.TraceRepresentation`.

No equality with a concrete traced Bastin energy integral is asserted here. A downstream consumer
must supply a `RegularizedStredaRepresentation` for the static vertex response, including all
analytic and energy-representation hypotheses required by the Středa layer.
-/

namespace QuantumTheory
namespace Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι]

/-- Zero-frequency finite spectral response of the measured/source vertices only, before adding the
explicit observable-variation expectation. -/
noncomputable def finiteStaticKuboBastinChannelVertexResponse
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel H)
    (eta : ℝ) : ℂ :=
  ∑ mn : ι × ι,
    purePointKuboBastinSpectralVertexTerm
      system data channel.measured channel.source 0 eta mn

/-- Zero-frequency specialization of the complete finite spectral Kubo–Bastin response. The
switching rate stays finite and the explicit observable-variation expectation is retained. -/
noncomputable def finiteStaticKuboBastinChannelResponse
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel H)
    (eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralChannelResponse system data channel 0 eta

/-- The static generalized response is exactly the two-vertex spectral response plus the explicit
observable-variation expectation. -/
theorem finiteStaticKuboBastinChannelResponse_eq_vertex_add_observableVariation
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel H)
    (eta : ℝ) :
    finiteStaticKuboBastinChannelResponse system data channel eta =
      finiteStaticKuboBastinChannelVertexResponse system data channel eta +
        purePointNormalizedExpectation system data channel.observableVariation := by
  rfl

/-- At positive switching rate, the zero-frequency causal response carried by the channel equals the
named finite static spectral Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainResponseChannel_zero_frequency_eq_staticKuboBastin
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel H)
    (eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source 0 eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteStaticKuboBastinChannelResponse system data channel eta := by
  simpa [finiteStaticKuboBastinChannelResponse] using
    adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
      system data channel 0 eta heta

/-- Once the static two-vertex response is equipped with an explicit regularized Středa energy
representation, the complete generalized response is its surface-plus-sea decomposition plus the
unchanged observable-variation expectation. -/
theorem finiteStaticKuboBastinChannelResponse_eq_surface_add_sea_add_observableVariation
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel H)
    (eta : ℝ)
    (representation : RegularizedStredaRepresentation
      (finiteStaticKuboBastinChannelVertexResponse system data channel eta)) :
    finiteStaticKuboBastinChannelResponse system data channel eta =
      (regularizedStredaFermiSurface representation.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea representation.toRegularizedStredaIntegralData) +
      purePointNormalizedExpectation system data channel.observableVariation := by
  rw [finiteStaticKuboBastinChannelResponse_eq_vertex_add_observableVariation]
  exact congrArg
    (fun response : ℂ =>
      response + purePointNormalizedExpectation system data channel.observableVariation)
    representation.response_eq_surface_add_sea

end
end Transport
end QuantumTheory

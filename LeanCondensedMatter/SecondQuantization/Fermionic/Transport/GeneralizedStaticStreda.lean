import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.Transport.FiniteKuboBastin
import LeanCondensedMatter.Transport.StredaIntegration

set_option linter.style.header false

/-!
# Static generalized Kubo–Bastin response and Středa boundary

The generalized finite Kubo–Bastin layer keeps three response-channel inputs independent:

```text
measured A₀
source B
observable variation A₁.
```

At zero driving frequency the ordinary finite-dimensional Bastin response therefore has two
conceptually distinct pieces:

```text
vertex response(A₀,B) + ⟨A₁⟩.
```

Only the two-vertex Bastin piece is fed into `RegularizedStredaRepresentation`.  The explicit
observable-variation/contact expectation remains outside the surface/sea integration-by-parts
split.  This avoids silently absorbing a source-dependent measured-observable variation into a
traced two-vertex energy kernel.

No equality with a concrete traced Bastin energy integral is asserted here.  A downstream consumer
must supply a `RegularizedStredaRepresentation` for the static vertex response, including all
analytic and energy-representation hypotheses required by the Středa layer.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site ι : Type*}
variable [Fintype Site] [Fintype ι]

/-- Zero-frequency ordinary-trace response of the measured/source vertices only, before adding the
explicit observable-variation expectation. -/
noncomputable def finiteDimensionalStaticKuboBastinChannelVertexResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (eta : ℝ) : ℂ :=
  LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
    (finiteKuboBastinVertexTraceCarrier
      system data channel.measured channel.source 0 eta)

/-- Zero-frequency specialization of the complete generalized Kubo–Bastin response.  The switching
rate stays finite and the explicit observable-variation expectation is retained. -/
noncomputable def finiteDimensionalStaticKuboBastinChannelResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (eta : ℝ) : ℂ :=
  finiteDimensionalKuboBastinChannelResponse system data channel 0 eta

/-- The static generalized response is exactly the two-vertex ordinary trace plus the explicit
observable-variation/contact expectation. -/
theorem finiteDimensionalStaticKuboBastinChannelResponse_eq_vertex_add_observableVariation
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (eta : ℝ) :
    finiteDimensionalStaticKuboBastinChannelResponse system data channel eta =
      finiteDimensionalStaticKuboBastinChannelVertexResponse system data channel eta +
        purePointNormalizedExpectation system data channel.observableVariation := by
  rfl

/-- At positive switching rate, the zero-frequency causal response carried by the channel equals the
named static generalized Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainResponseChannel_zero_frequency_eq_staticKuboBastin
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source 0 eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteDimensionalStaticKuboBastinChannelResponse system data channel eta := by
  simpa [finiteDimensionalStaticKuboBastinChannelResponse] using
    adiabaticFrequencyDomainResponseChannel_eq_finiteDimensionalKuboBastin
      system data channel 0 eta heta

/-- Once the static two-vertex response is equipped with an explicit regularized Středa energy
representation, the complete generalized response is its surface-plus-sea decomposition plus the
unchanged observable-variation/contact expectation. -/
theorem finiteDimensionalStaticKuboBastinChannelResponse_eq_surface_add_sea_add_observableVariation
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (eta : ℝ)
    (representation : RegularizedStredaRepresentation
      (finiteDimensionalStaticKuboBastinChannelVertexResponse system data channel eta)) :
    finiteDimensionalStaticKuboBastinChannelResponse system data channel eta =
      (regularizedStredaFermiSurface representation.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea representation.toRegularizedStredaIntegralData) +
      purePointNormalizedExpectation system data channel.observableVariation := by
  rw [finiteDimensionalStaticKuboBastinChannelResponse_eq_vertex_add_observableVariation]
  exact congrArg
    (fun response : ℂ =>
      response + purePointNormalizedExpectation system data channel.observableVariation)
    representation.response_eq_surface_add_sea

end
end Transport
end Fermionic
end SecondQuantization

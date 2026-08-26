import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentKuboBastin
import LeanCondensedMatter.Transport.Streda.GeneralizedStatic

set_option linter.style.header false

/-!
# Corrected-current static Kubo–Bastin and Středa specialization

This module specializes the generalized static response-channel boundary to the corrected/nested
current representation. The static target is the zero-frequency finite spectral Kubo–Bastin
response; no artificial finite-dimensional trace carrier is introduced.

The source vertex and explicit first-order observable variation remain independent. Consequently,
the Středa surface/sea decomposition is applied only to the measured/source two-vertex response;
the observable-variation/contact expectation stays explicit.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site OneForm ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable [Fintype ι]

/-- Zero-frequency finite spectral Kubo–Bastin response of one corrected current component. -/
noncomputable def finiteStaticCorrectedCurrentKuboBastinResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralCorrectedCurrentResponse system data
    velocity m N α source observableVariation 0 eta

/-- At positive switching rate, the zero-frequency causal response of the corrected current equals
its named finite static spectral Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainCorrectedCurrent_zero_frequency_eq_staticKuboBastin
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          (boundedCorrectedCurrentObservable velocity m N α)
          source 0 eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteStaticCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation eta := by
  simpa [finiteStaticCorrectedCurrentKuboBastinResponse,
    finiteKuboBastinSpectralCorrectedCurrentResponse,
    correctedCurrentResponseChannel] using
    adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
      system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation)
        0 eta heta

/-- Given an explicit Středa representation for the corrected-current measured/source vertex
response, the complete static response is its Fermi-surface plus Fermi-sea decomposition together
with the unchanged observable-variation/contact expectation. -/
theorem finiteStaticCorrectedCurrentKuboBastinResponse_eq_surface_add_sea_add_observableVariation
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (eta : ℝ)
    (representation : RegularizedStredaRepresentation
      (finiteStaticKuboBastinChannelVertexResponse system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation) eta)) :
    finiteStaticCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation eta =
      (regularizedStredaFermiSurface representation.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea representation.toRegularizedStredaIntegralData) +
      purePointNormalizedExpectation system data observableVariation := by
  change finiteStaticKuboBastinChannelResponse system data
      (correctedCurrentResponseChannel velocity m N α source observableVariation) eta = _
  simpa [correctedCurrentResponseChannel] using
    finiteStaticKuboBastinChannelResponse_eq_surface_add_sea_add_observableVariation
      system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation)
        eta representation

end
end Transport
end Fermionic
end SecondQuantization

import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentKuboBastin
import LeanCondensedMatter.Transport.Streda.GeneralizedStatic

set_option linter.style.header false

/-!
# Corrected-current static Kubo–Bastin and Středa specialization

This module specializes the generalized static response-channel boundary to the corrected/nested
current representation.  The transported one-body observable `m` remains arbitrary, so the same
API covers corrected spin and orbital current observables by choosing the corresponding internal
operator.

The source vertex and explicit first-order observable variation remain independent.  Consequently,
the Středa surface/sea decomposition is applied only to the measured/source two-vertex response;
the observable-variation/contact expectation stays explicit:

```text
corrected-current static response
  = vertex Bastin(J_corrected, B) + ⟨A₁⟩
  = Fermi surface + Fermi sea + ⟨A₁⟩.
```

No Středa representation is manufactured automatically.  The final theorem requires an explicit
`RegularizedStredaRepresentation` for the corrected-current vertex response, preserving the
analytic and energy-representation hypotheses of the downstream Středa layer.
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

/-- Zero-frequency finite-dimensional Kubo–Bastin response of one corrected current component. -/
noncomputable def finiteDimensionalStaticCorrectedCurrentKuboBastinResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (eta : ℝ) : ℂ :=
  finiteDimensionalStaticKuboBastinChannelResponse system data
    (correctedCurrentResponseChannel velocity m N α source observableVariation) eta

/-- The static corrected-current response is exactly the zero-frequency specialization of the
finite-frequency corrected-current Kubo–Bastin response. -/
theorem finiteDimensionalCorrectedCurrentKuboBastinResponse_zero_frequency_eq_static
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (eta : ℝ) :
    finiteDimensionalCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation 0 eta =
      finiteDimensionalStaticCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation eta := by
  rfl

/-- At positive switching rate, the zero-frequency causal response of the corrected current equals
its named static Kubo–Bastin response. -/
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
      finiteDimensionalStaticCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation eta := by
  simpa [finiteDimensionalStaticCorrectedCurrentKuboBastinResponse,
    correctedCurrentResponseChannel] using
    adiabaticFrequencyDomainResponseChannel_zero_frequency_eq_staticKuboBastin
      system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation)
        eta heta

/-- Given an explicit Středa representation for the corrected-current measured/source vertex
response, the complete static response is its Fermi-surface plus Fermi-sea decomposition together
with the unchanged observable-variation/contact expectation. -/
theorem finiteDimensionalStaticCorrectedCurrentKuboBastinResponse_eq_surface_add_sea_add_observableVariation
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (eta : ℝ)
    (representation : RegularizedStredaRepresentation
      (finiteDimensionalStaticKuboBastinChannelVertexResponse system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation) eta)) :
    finiteDimensionalStaticCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation eta =
      (regularizedStredaFermiSurface representation.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea representation.toRegularizedStredaIntegralData) +
      purePointNormalizedExpectation system data observableVariation := by
  simpa [finiteDimensionalStaticCorrectedCurrentKuboBastinResponse,
    correctedCurrentResponseChannel] using
    finiteDimensionalStaticKuboBastinChannelResponse_eq_surface_add_sea_add_observableVariation
      system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation)
        eta representation

end
end Transport
end Fermionic
end SecondQuantization

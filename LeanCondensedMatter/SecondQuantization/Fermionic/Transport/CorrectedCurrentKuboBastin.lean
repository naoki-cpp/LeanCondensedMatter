import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.GeneralizedKuboBastin

set_option linter.style.header false

/-!
# Corrected-current Kubo–Bastin bridge

This module feeds the corrected/nested current representation from `CorrectedCurrentResponse`
directly into the neutral `ResponseChannel` and generalized finite Kubo–Bastin API.

For a supplied transported one-body observable `m`, velocity `v`, localizer-valued one-form `N`,
and one-form `α`, the measured one-body current is

```text
J_corrected(α) = J_nested(α)
               = J_conv(α) + 1/4 [v,[N α,m]].
```

The construction is intentionally generic in `m`. Choosing an internal spin operator gives a
corrected spin-current channel; choosing an orbital/internal angular-momentum operator gives the
corresponding orbital-current channel. The electric or other source vertex and the explicit
first-order observable variation remain independent inputs.

No global-current uniqueness, DC limit, zero-broadening limit, disorder average, trace per unit
volume, thermodynamic limit, or Středa decomposition is introduced here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory QuantumTheory.LinearResponse

noncomputable section

variable {Site OneForm ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable [Fintype ι]

/-- Bounded Fock-space observable associated with one corrected/nested current component. -/
noncomputable def boundedCorrectedCurrentObservable
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator
    (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
      (LatticeState Site) velocity m N α)

/-- Neutral response channel for one corrected current component.

`source` and `observableVariation` are deliberately supplied independently: generalized spin or
orbital currents may be measured in response to an electric source while also carrying their own
explicit first-order source dependence. -/
noncomputable def correctedCurrentResponseChannel
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :
    ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedCorrectedCurrentObservable velocity m N α
  source := source
  observableVariation := observableVariation

/-- Finite spectral Kubo–Bastin response of a corrected current channel. -/
noncomputable def finiteKuboBastinSpectralCorrectedCurrentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralChannelResponse system data
    (correctedCurrentResponseChannel velocity m N α source observableVariation)
    omega eta

/-- Ordinary finite-dimensional Kubo–Bastin response of a corrected current channel. -/
noncomputable def finiteDimensionalCorrectedCurrentKuboBastinResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) : ℂ :=
  finiteDimensionalKuboBastinChannelResponse system data
    (correctedCurrentResponseChannel velocity m N α source observableVariation)
    omega eta

/-- The corrected-current finite trace response is exactly its generalized spectral
Kubo–Bastin response. -/
theorem finiteDimensionalCorrectedCurrentKuboBastinResponse_eq_spectral
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    finiteDimensionalCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation omega eta =
      finiteKuboBastinSpectralCorrectedCurrentResponse system data
        velocity m N α source observableVariation omega eta := by
  exact finiteDimensionalKuboBastinVertexResponse_eq_spectral system data
    (boundedCorrectedCurrentObservable velocity m N α)
    source observableVariation omega eta

/-- At positive switching rate, the causal frequency-domain response of the corrected current
channel is exactly its ordinary finite-dimensional Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainCorrectedCurrent_eq_finiteDimensionalKuboBastin
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          (boundedCorrectedCurrentObservable velocity m N α)
          source omega eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteDimensionalCorrectedCurrentKuboBastinResponse system data
        velocity m N α source observableVariation omega eta := by
  simpa [finiteDimensionalCorrectedCurrentKuboBastinResponse,
    correctedCurrentResponseChannel] using
    adiabaticFrequencyDomainResponseChannel_eq_finiteDimensionalKuboBastin
      system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation)
        omega eta heta

end
end Transport
end Fermionic
end SecondQuantization

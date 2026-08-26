import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentResponse
import LeanCondensedMatter.Transport.KuboBastin.Finite

set_option linter.style.header false

/-!
# Corrected-current Kubo–Bastin bridge

This module feeds the corrected/nested current representation from `CorrectedCurrentResponse`
directly into the neutral `ResponseChannel` and generalized finite spectral Kubo–Bastin API.

For a supplied transported one-body observable `m`, velocity `v`, localizer-valued one-form `N`,
and one-form `α`, the measured one-body current is

```text
J_corrected(α) = J_nested(α)
               = J_conv(α) + 1/4 [v,[N α,m]].
```

The electric or other source vertex and the explicit first-order observable variation remain
independent inputs. No artificial ordinary-trace carrier is introduced here; genuine operator
traces belong to the canonical static Bastin/Středa layer.
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

noncomputable def boundedCorrectedCurrentObservable
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator
    (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
      (LatticeState Site) velocity m N α)

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

/-- At positive switching rate, the causal frequency-domain response of the corrected current
channel is exactly its finite spectral Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainCorrectedCurrent_eq_bastinSpectral
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
      finiteKuboBastinSpectralCorrectedCurrentResponse system data
        velocity m N α source observableVariation omega eta := by
  simpa [finiteKuboBastinSpectralCorrectedCurrentResponse,
    correctedCurrentResponseChannel] using
    adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
      system data
        (correctedCurrentResponseChannel velocity m N α source observableVariation)
        omega eta heta

end
end Transport
end Fermionic
end SecondQuantization

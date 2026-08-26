import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel
import LeanCondensedMatter.Transport.KuboBastin.PurePoint

set_option linter.style.header false

/-!
# Finite-sum pure-point Kubo–Bastin response

This module owns the finite spectral-index specialization of the pure-point Kubo–Bastin bridge.
The upstream transition algebra in `KuboBastin.PurePoint` does not assume a finite index type;
`Fintype ι` first enters here when the transition family is assembled as an ordinary finite sum.

```text
pure-point spectral transition
  -> finite two-vertex sum
  -> explicit observable variation
  -> ResponseChannel packaging.
```

Genuine ordinary finite-dimensional trace realizations are downstream in the canonical static
Bastin/Středa layer under `Transport.Streda`, where finite dimensionality of the Hilbert-space
carrier first enters. No zero-frequency, zero-broadening, disorder, trace-per-unit-volume, or
thermodynamic-limit statement is introduced here.
-/

namespace QuantumTheory
namespace Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι]
variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- Finite two-vertex pure-point Kubo–Bastin sum before adding any explicit first-order observable
variation. This is the part later eligible for a Středa energy representation. -/
noncomputable def finiteKuboBastinSpectralVertexSum
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  ∑ mn : ι × ι,
    purePointKuboBastinSpectralVertexTerm
      system data measured source omega eta mn

/-- At positive switching rate, the causal two-vertex susceptibility is exactly the finite
Kubo–Bastin spectral vertex sum. -/
theorem adiabaticFrequencyDomainSusceptibility_eq_bastinSpectralVertexSum
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (purePointNormalizedExpectation system data)
        measured source omega eta heta =
      finiteKuboBastinSpectralVertexSum system data measured source omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
    system data measured source omega eta heta]
  unfold finiteKuboBastinSpectralVertexSum
  apply Finset.sum_congr rfl
  intro mn _
  exact purePointLehmannVertexTerm_eq_bastinSpectral
    system data measured source omega eta heta mn

/-- Finite pure-point Kubo–Bastin response coefficient for supplied measured/source vertices and an
explicit first-order observable variation. -/
noncomputable def finiteKuboBastinSpectralVertexResponse
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralVertexSum system data measured source omega eta +
    purePointNormalizedExpectation system data observableVariation

/-- The generic fixed-positive-rate frequency-domain susceptibility plus the explicit
observable-variation term is exactly the finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          measured source omega eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta := by
  rw [adiabaticFrequencyDomainSusceptibility_eq_bastinSpectralVertexSum
    system data measured source omega eta heta]
  rfl

/-- The finite spectral Kubo–Bastin response attached directly to a neutral `ResponseChannel`. -/
noncomputable def finiteKuboBastinSpectralChannelResponse
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralVertexResponse system data
    channel.measured channel.source channel.observableVariation omega eta

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
    (channel : ResponseChannel H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteKuboBastinSpectralChannelResponse system data channel omega eta := by
  simpa [finiteKuboBastinSpectralChannelResponse] using
    adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
      system data channel.measured channel.source channel.observableVariation omega eta heta

end
end Transport
end QuantumTheory

import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel
import LeanCondensedMatter.Transport.KuboBastin.Eigenbasis

set_option linter.style.header false

/-!
# Finite-sum eigenbasis Kubo–Bastin response

This module owns the finite spectral-index specialization of the eigenbasis Kubo–Bastin bridge.
The upstream transition algebra in `KuboBastin.Eigenbasis` does not assume a finite index type;
`Fintype ι` first enters here when the transition family is assembled as an ordinary finite sum.

```text
eigenbasis spectral transition
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
  (data : EnergyEigenbasisLehmannData system ι)

/-- Finite two-vertex eigenbasis Kubo–Bastin sum before adding any explicit first-order observable
variation. This is the part later eligible for a Středa energy representation. -/
noncomputable def finiteKuboBastinSpectralVertexSum
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  ∑ mn : ι × ι,
    eigenbasisKuboBastinSpectralVertexTerm
      system data measured source omega eta mn

/-- At positive switching rate, the causal two-vertex susceptibility is exactly the finite
Kubo–Bastin spectral vertex sum. -/
theorem adiabaticFrequencyDomainSusceptibility_eq_bastinSpectralVertexSum
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        (eigenbasisNormalizedExpectation system data)
        measured source omega eta heta =
      finiteKuboBastinSpectralVertexSum system data measured source omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eigenbasis_eq_finite_sum
    system data measured source omega eta heta]
  unfold finiteKuboBastinSpectralVertexSum
  apply Finset.sum_congr rfl
  intro mn _
  exact eigenbasisLehmannVertexTerm_eq_bastinSpectral
    system data measured source omega eta heta mn

/-- The finite spectral Kubo–Bastin response attached directly to a neutral `ResponseChannel`. -/
noncomputable def finiteKuboBastinSpectralChannelResponse
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralVertexSum
      system data channel.measured channel.source omega eta +
    eigenbasisNormalizedExpectation system data channel.observableVariation

/-- The channel response reduces to its aggregate spectral vertex sum. -/
theorem finiteKuboBastinSpectralChannelResponse_eq_vertexSum
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteKuboBastinSpectralChannelResponse system data channel omega eta =
      finiteKuboBastinSpectralVertexSum system data channel.measured channel.source omega eta +
        eigenbasisNormalizedExpectation system data channel.observableVariation := by
  rfl

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
    (channel : ResponseChannel H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (eigenbasisNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        eigenbasisNormalizedExpectation system data channel.observableVariation =
      finiteKuboBastinSpectralChannelResponse system data channel omega eta := by
  simpa only [finiteKuboBastinSpectralChannelResponse] using
    congrArg
      (fun response : ℂ =>
        response + eigenbasisNormalizedExpectation system data channel.observableVariation)
      (adiabaticFrequencyDomainSusceptibility_eq_bastinSpectralVertexSum
        system data channel.measured channel.source omega eta heta)

end
end Transport
end QuantumTheory

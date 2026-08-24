import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite
import LeanCondensedMatter.Transport.KuboBastin.Finite

set_option linter.style.header false

/-!
# Finite-dimensional trace realization of Kubo–Bastin response

This module owns the ordinary finite-dimensional trace realization of the finite spectral-index
response from `KuboBastin.Finite`. The pure-point transition algebra itself lives upstream in
`KuboBastin.PurePoint` without a finite-index assumption. `Fintype ι` enters in `KuboBastin.Finite`;
finite dimensionality of the Hilbert-space carrier enters only here through `LinearMap.trace`.

No zero-frequency, zero-broadening, disorder, trace-per-unit-volume, or thermodynamic-limit
statement is introduced here.
-/

namespace QuantumTheory
namespace Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [FiniteDimensional ℂ H]
variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- Ordinary finite-dimensional trace carrier for the generic measured/source Kubo–Bastin
response. -/
noncomputable def finiteKuboBastinVertexTraceCarrier
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) : H →ₗ[ℂ] H :=
  (∑ mn : ι × ι,
      purePointKuboBastinSpectralVertexTerm
        system data measured source omega eta mn) •
    ((purePointDensityOperator system data).op : H →ₗ[ℂ] H)

/-- Expanding the generic ordinary trace carrier gives the finite retarded-resolvent spectral sum. -/
theorem linearMap_trace_finiteKuboBastinVertexTraceCarrier
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) :
    LinearMap.trace ℂ H
        (finiteKuboBastinVertexTraceCarrier
          system data measured source omega eta) =
      ∑ mn : ι × ι,
        purePointKuboBastinSpectralVertexTerm
          system data measured source omega eta mn := by
  unfold finiteKuboBastinVertexTraceCarrier
  rw [map_smul]
  rw [DensityOperator.linearMap_trace_eq_one]
  simp

/-- Generic ordinary finite-dimensional Kubo–Bastin response with the observable variation kept as
an explicit expectation value. -/
noncomputable def finiteDimensionalKuboBastinVertexResponse
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  LinearMap.trace ℂ H
      (finiteKuboBastinVertexTraceCarrier
        system data measured source omega eta) +
    purePointNormalizedExpectation system data observableVariation

/-- The generic ordinary-trace response is exactly its finite spectral form. -/
theorem finiteDimensionalKuboBastinVertexResponse_eq_spectral
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) :
    finiteDimensionalKuboBastinVertexResponse
        system data measured source observableVariation omega eta =
      finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta := by
  unfold finiteDimensionalKuboBastinVertexResponse
    finiteKuboBastinSpectralVertexResponse
  rw [linearMap_trace_finiteKuboBastinVertexTraceCarrier]

/-- The generic fixed-positive-rate response plus observable variation equals the ordinary
finite-dimensional Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_finiteDimensionalKuboBastin
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          measured source omega eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteDimensionalKuboBastinVertexResponse
        system data measured source observableVariation omega eta := by
  rw [adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
    system data measured source observableVariation omega eta heta]
  exact (finiteDimensionalKuboBastinVertexResponse_eq_spectral
    system data measured source observableVariation omega eta).symm

/-- The ordinary finite-dimensional Kubo–Bastin response attached directly to a neutral
`ResponseChannel`. -/
noncomputable def finiteDimensionalKuboBastinChannelResponse
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteDimensionalKuboBastinVertexResponse system data
    channel.measured channel.source channel.observableVariation omega eta

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its ordinary finite-dimensional Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_finiteDimensionalKuboBastin
    (channel : ResponseChannel H)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteDimensionalKuboBastinChannelResponse system data channel omega eta := by
  simpa [finiteDimensionalKuboBastinChannelResponse] using
    adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_finiteDimensionalKuboBastin
      system data channel.measured channel.source channel.observableVariation omega eta heta

end
end Transport
end QuantumTheory

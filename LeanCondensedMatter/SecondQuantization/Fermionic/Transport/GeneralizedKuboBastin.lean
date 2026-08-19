import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinTrace
import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointFrequencyDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel

set_option linter.style.header false

/-!
# Generalized finite-dimensional Kubo–Bastin response

The generic causal Kubo layer packages a measured observable, source vertex, and first-order
observable variation in `ResponseChannel`.  The older finite Kubo–Bastin transport path specialized
these inputs immediately to the continuity-derived electric current and Peierls contact operator.

This module keeps the finite pure-point Bastin bridge generic in those response vertices:

```text
ResponseChannel
  measured A
  source B
  observable variation A₁
    -> finite Lehmann response + ⟨A₁⟩
    -> finite retarded-resolvent spectral response + ⟨A₁⟩
    -> ordinary finite-dimensional trace response + ⟨A₁⟩.
```

The existing directional charge-conductivity API is recovered as a specialization theorem. No
zero-frequency, zero-broadening, disorder, trace-per-unit-volume, or thermodynamic-limit statement
is introduced here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice
open QuantumTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site ι : Type*}
variable [Fintype Site]

/-- One finite Kubo–Bastin transition for supplied measured and source vertices.

The resolvent is attached to the source-side spectral index exactly as in the directional-current
specialization. -/
noncomputable def finiteKuboBastinSpectralVertexTerm
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  -(((data.probability mn.1 - data.probability mn.2 : ℝ) : ℂ)) *
    inner ℂ (data.basis mn.1) (measured (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (source (data.basis mn.1)) *
    inner ℂ (data.basis mn.2)
      (retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis mn.2))

/-- At positive switching rate, a generic finite Lehmann transition equals its retarded-resolvent
Kubo–Bastin form. -/
theorem finiteLehmannVertexTerm_eq_bastinSpectral
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (heta : 0 < eta) (mn : ι × ι) :
    lehmannTerm system.hbar omega eta
        (data.energy mn.1 - data.energy mn.2)
        (purePointTransitionWeight system data measured source mn) =
      finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn := by
  have hhbar : system.hbar ≠ 0 := ne_of_gt system.hbar_pos
  have hhbarComplex : (system.hbar : ℂ) ≠ 0 := by
    exact_mod_cast hhbar
  have hshift := retardedSpectralShift_ne_zero system.hbar omega eta
    (data.energy mn.1) (data.energy mn.2) system.hbar_pos heta
  unfold lehmannTerm
  rw [lehmannDenominator_eq_retardedSpectralShift
    system.hbar omega eta (data.energy mn.1) (data.energy mn.2) hhbar]
  unfold finiteKuboBastinSpectralVertexTerm
  rw [inner_purePointBasis_retardedResolvent system data omega eta heta mn.1 mn.2]
  unfold purePointTransitionWeight
  field_simp [hhbar, hhbarComplex, hshift]

variable [Fintype ι]

/-- Finite pure-point Kubo–Bastin response coefficient for supplied measured/source vertices and an
explicit first-order observable variation. -/
noncomputable def finiteKuboBastinSpectralVertexResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) : ℂ :=
  (∑ mn : ι × ι,
      finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn) +
    purePointNormalizedExpectation system data observableVariation

/-- The generic fixed-positive-rate frequency-domain susceptibility plus the explicit
observable-variation term is exactly the finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          measured source omega eta heta +
        purePointNormalizedExpectation system data observableVariation =
      finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
    system data measured source omega eta heta]
  unfold finiteKuboBastinSpectralVertexResponse
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteLehmannVertexTerm_eq_bastinSpectral
    system data measured source omega eta heta mn

/-- Ordinary finite-dimensional trace carrier for the generic measured/source Kubo–Bastin
response. -/
noncomputable def finiteKuboBastinVertexTraceCarrier
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site :=
  (∑ mn : ι × ι,
      finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn) •
    ((purePointDensityOperator system data).op :
      FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site)

/-- Expanding the generic ordinary trace carrier gives the finite retarded-resolvent spectral sum. -/
theorem linearMap_trace_finiteKuboBastinVertexTraceCarrier
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
        (finiteKuboBastinVertexTraceCarrier
          system data measured source omega eta) =
      ∑ mn : ι × ι,
        finiteKuboBastinSpectralVertexTerm
          system data measured source omega eta mn := by
  unfold finiteKuboBastinVertexTraceCarrier
  rw [map_smul]
  rw [DensityOperator.linearMap_trace_eq_one]
  simp

/-- Generic ordinary finite-dimensional Kubo–Bastin response with the observable variation kept as
an explicit expectation value. -/
noncomputable def finiteDimensionalKuboBastinVertexResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) : ℂ :=
  LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
      (finiteKuboBastinVertexTraceCarrier
        system data measured source omega eta) +
    purePointNormalizedExpectation system data observableVariation

/-- The generic ordinary-trace response is exactly its finite spectral form. -/
theorem finiteDimensionalKuboBastinVertexResponse_eq_spectral
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
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
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
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

/-- The spectral Kubo–Bastin response attached directly to a neutral `ResponseChannel`. -/
noncomputable def finiteKuboBastinSpectralChannelResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralVertexResponse system data
    channel.measured channel.source channel.observableVariation omega eta

/-- The ordinary finite-dimensional Kubo–Bastin response attached directly to a neutral
`ResponseChannel`. -/
noncomputable def finiteDimensionalKuboBastinChannelResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) : ℂ :=
  finiteDimensionalKuboBastinVertexResponse system data
    channel.measured channel.source channel.observableVariation omega eta

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its finite Kubo–Bastin spectral response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteKuboBastinSpectralChannelResponse system data channel omega eta := by
  simpa [finiteKuboBastinSpectralChannelResponse] using
    adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_bastinSpectral
      system data channel.measured channel.source channel.observableVariation omega eta heta

/-- At positive switching rate, the frequency-domain response carried by a `ResponseChannel` is
exactly its ordinary finite-dimensional Kubo–Bastin response. -/
theorem adiabaticFrequencyDomainResponseChannel_eq_finiteDimensionalKuboBastin
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) (heta : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
          (purePointNormalizedExpectation system data)
          channel.measured channel.source omega eta heta +
        purePointNormalizedExpectation system data channel.observableVariation =
      finiteDimensionalKuboBastinChannelResponse system data channel omega eta := by
  simpa [finiteDimensionalKuboBastinChannelResponse] using
    adiabaticFrequencyDomainSusceptibility_add_observableVariation_eq_finiteDimensionalKuboBastin
      system data channel.measured channel.source channel.observableVariation omega eta heta

variable {E : Type*}
variable [LinearOrder Site]
variable [AddCommGroup E] [Module ℝ E]

/-- The existing directional charge-conductivity Kubo–Bastin path is the specialization with both
response vertices equal to the continuity-derived current and the observable variation equal to the
Peierls contact operator. -/
theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_vertexResponse
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteDimensionalKuboBastinVertexResponse system data
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          omega eta *
        finiteVolumeConductivityNormalization convention omega eta := by
  rfl

/-- Neutral response-channel packaging of the existing directional charge-current/Peierls-contact
specialization. -/
noncomputable def directionalChargeResponseChannel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  source := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  observableVariation := boundedDirectionalContact geometry direction
    (system.hbar : ℂ) (q : ℂ) K

/-- The existing directional finite-dimensional Kubo–Bastin conductivity is recovered from the
neutral `ResponseChannel` specialization, followed only by the existing finite-volume/electric-field
normalization. -/
theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_channelResponse
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteDimensionalKuboBastinChannelResponse system data
          (directionalChargeResponseChannel system geometry direction K q)
          omega eta *
        finiteVolumeConductivityNormalization convention omega eta := by
  rw [finiteDimensionalKuboBastinDirectionalConductivity_eq_vertexResponse]
  rfl

end
end Transport
end Fermionic
end SecondQuantization

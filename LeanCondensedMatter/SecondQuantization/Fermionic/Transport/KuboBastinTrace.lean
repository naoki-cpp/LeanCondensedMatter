import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral

set_option linter.style.header false

/-!
# Ordinary finite-dimensional trace form of the directional Kubo–Bastin response

This module specializes the neutral finite Kubo–Bastin response from `Transport.FiniteKuboBastin`
to the continuity-derived directional electric current and Peierls contact operator. The directional
trace carrier is defined from the generic measured/source trace carrier rather than duplicating its
implementation.

This is the finite equivalent permitted at the B2 boundary of issue #367. It is basis-resolved
through the scalar coefficient because the resolvent energy `Eₘ + ℏω` depends on the outer
spectral index. The main theorem does not introduce a disconnected Bastin law: it proves that the
named trace response is equal to the conductivity already obtained through time-dependent
perturbation theory, the causal Kubo theorem, the finite observation-time limit, and the
Kubo–Greenwood expansion.

The current, Hamiltonian, pure-point Fermi probabilities, Peierls contact expectation, positive
finite volume, electric-field conversion factor, frequency, and positive switching rate remain
explicit. No cyclic energy-integral formula, zero-broadening limit, DC limit, disorder average,
trace per unit volume, or thermodynamic limit is claimed.

A future infinite-dimensional finite-volume extension would require an actual complex trace ideal
for the generally non-self-adjoint current–resolvent products, closure of that ideal under bounded
left and right multiplication, cyclicity for bounded/trace-class products, and integrability of the
energy-dependent trace. Those ingredients are not presently available in the repository and are
not replaced here by compactness or by a self-adjoint spectral trace. Trace per unit volume and the
thermodynamic limit remain separate constructions.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

open QuantumTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- Neutral response-channel packaging of the directional charge-current/Peierls-contact
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

/-- Finite-dimensional trace carrier for the regularized Kubo–Bastin current-current response.

This is the generic measured/source trace carrier specialized to the continuity-derived
directional current at both response vertices. -/
noncomputable def finiteKuboBastinDirectionalTraceCarrier
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site :=
  finiteKuboBastinVertexTraceCarrier system data
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta

/-- Expanding the specialized ordinary trace carrier gives the directional finite
retarded-resolvent spectral sum. -/
theorem linearMap_trace_finiteKuboBastinDirectionalTraceCarrier
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
        (finiteKuboBastinDirectionalTraceCarrier
          system data geometry direction K q omega eta) =
      ∑ mn : ι × ι,
        finiteKuboBastinSpectralDirectionalCurrentTerm
          system data geometry direction K q omega eta mn := by
  unfold finiteKuboBastinDirectionalTraceCarrier
  rw [linearMap_trace_finiteKuboBastinVertexTraceCarrier]
  rfl

/-- Named ordinary finite-dimensional Kubo–Bastin conductivity.

The current-current trace is the generic trace response specialized to the directional current; the
Peierls contact expectation and the finite-volume electric-field normalization remain separate and
explicit. -/
noncomputable def finiteDimensionalKuboBastinDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℂ :=
  (LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
      (finiteKuboBastinDirectionalTraceCarrier
        system data geometry direction K q omega eta) +
    purePointNormalizedExpectation system data
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization convention omega eta

/-- The directional charge conductivity is the generic vertex response specialized to the
continuity-derived current/current pair and Peierls contact operator, followed only by the existing
finite-volume/electric-field normalization. -/
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

/-- The directional charge conductivity is equivalently the neutral `ResponseChannel`
specialization, followed only by the existing finite-volume/electric-field normalization. -/
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
  rfl

/-- The ordinary trace definition has exactly the finite spectral/Lehmann representation proved in
`KuboBastinSpectral`. -/
theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_spectral
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention := by
  unfold finiteDimensionalKuboBastinDirectionalConductivity
    finiteKuboBastinSpectralDirectionalConductivity
  rw [linearMap_trace_finiteKuboBastinDirectionalTraceCarrier]

/-- Main B2 identification: the ordinary finite-dimensional Kubo–Bastin trace response is exactly
the conductivity derived from the causal Kubo response chain, at fixed positive switching rate. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_eq_finiteDimensionalKuboBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (heta : 0 < eta) :
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta := by
  calc
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteKuboGreenwoodDirectionalConductivity
        convention system data geometry direction K q omega eta :=
      infiniteTimeAdiabaticDirectionalConductivity_eq_finiteKuboGreenwood
        convention system data geometry direction K q omega eta heta
    _ = finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention :=
      finiteKuboGreenwoodDirectionalConductivity_eq_bastinSpectral
        system data geometry direction K q omega eta convention heta
    _ = finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta :=
      (finiteDimensionalKuboBastinDirectionalConductivity_eq_spectral
        convention system data geometry direction K q omega eta).symm

end
end Transport
end Fermionic
end SecondQuantization

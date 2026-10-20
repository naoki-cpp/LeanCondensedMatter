import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood
import LeanCondensedMatter.Transport.KuboBastin.Finite

set_option linter.style.header false

/-!
# Fermionic directional Kubo–Bastin spectral conductivity

This module specializes the statistics-independent Kubo–Bastin transition algebra and finite
spectral-index response sums to the directional electric current of a finite fermionic lattice,
starting from the finite Kubo–Greenwood response.

The directional current, source, and Peierls contact are packaged as one `ResponseChannel` before
the generic response API is called. Transition terms remain at the raw vertex level.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable
  (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
  (data : EnergyEigenbasisLehmannData system ι)

variable [LinearOrder Site]
variable
  (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
  (K : LocallyFiniteHopping Site) (q omega eta : ℝ)

/-- Finite regularized directional Kubo–Bastin conductivity in spectral resolvent form, with the
Peierls contact term retained explicitly. -/
noncomputable def finiteKuboBastinSpectralDirectionalConductivity
    [Fintype ι] (convention : QuantumTheory.Transport.PositiveVolume) : ℂ :=
  finiteKuboBastinSpectralChannelResponse system data
      (boundedDirectionalResponseChannel system geometry direction K q)
      omega eta *
    finiteVolumeConductivityNormalization convention omega eta

/-- The finite spectral Kubo–Bastin resolvent form is exactly the finite Kubo–Greenwood
conductivity derived from the causal response chain. -/
theorem finiteKuboGreenwoodDirectionalConductivity_eq_bastinSpectral
    [Fintype ι]
    (convention : QuantumTheory.Transport.PositiveVolume) (heta : 0 < eta) :
    finiteKuboGreenwoodDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention := by
  unfold finiteKuboGreenwoodDirectionalConductivity
    finiteKuboBastinSpectralDirectionalConductivity
  rw [← adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_lehmannSeries
    system data _ _ omega eta heta (eigenbasisTimeDomainSummable_of_finite system data _ _)]
  exact congrArg (fun response : ℂ =>
    response * finiteVolumeConductivityNormalization convention omega eta)
    (adiabaticFrequencyDomainResponseChannel_eq_bastinSpectral system data
      (boundedDirectionalResponseChannel system geometry direction K q) omega eta heta)

/-- At every positive switching rate and arbitrary driving frequency, the causal conductivity
equals its finite spectral Bastin representation. Zero frequency is a specialization of this
identity, not a zero-switching or DC limit. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_eq_bastinSpectral
    [Fintype ι] (convention : QuantumTheory.Transport.PositiveVolume) (heta : 0 < eta) :
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (eigenbasisNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention :=
  (infiniteTimeAdiabaticDirectionalConductivity_eq_finiteKuboGreenwood
    convention system data geometry direction K q omega eta heta).trans
    (finiteKuboGreenwoodDirectionalConductivity_eq_bastinSpectral
      system data geometry direction K q omega eta convention heta)

end
end Transport
end Fermionic
end SecondQuantization

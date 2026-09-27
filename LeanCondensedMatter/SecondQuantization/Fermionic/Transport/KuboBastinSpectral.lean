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
  (data : PurePointLehmannData system ι)

variable [LinearOrder Site]
variable
  (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
  (K : LocallyFiniteHopping Site) (q omega eta : ℝ)

/-- One finite directional-current Kubo–Bastin spectral transition, specialized from the neutral
resolvent bridge to the continuity-derived electric current. -/
noncomputable def finiteKuboBastinSpectralDirectionalCurrentTerm
    (mn : ι × ι) : ℂ :=
  purePointKuboBastinSpectralVertexTerm system data
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta mn

/-- At positive switching rate, each directional Kubo–Greenwood term equals its retarded-resolvent
spectral form. -/
theorem finiteKuboGreenwoodDirectionalCurrentTerm_eq_bastinSpectral
    (heta : 0 < eta) (mn : ι × ι) :
    finiteKuboGreenwoodDirectionalCurrentTerm
        system data geometry direction K q omega eta mn =
      finiteKuboBastinSpectralDirectionalCurrentTerm
        system data geometry direction K q omega eta mn := by
  simpa [finiteKuboGreenwoodDirectionalCurrentTerm,
    finiteKuboBastinSpectralDirectionalCurrentTerm] using
    purePointLehmannVertexTerm_eq_bastinSpectral system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta heta mn

/-- The directional current, source, and Peierls contact form one response channel. -/
noncomputable def finiteDirectionalCurrentResponseChannel
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

/-- Finite regularized directional Kubo–Bastin conductivity in spectral resolvent form, with the
Peierls contact term retained explicitly. -/
noncomputable def finiteKuboBastinSpectralDirectionalConductivity
    [Fintype ι] (convention : QuantumTheory.Transport.PositiveVolume) : ℂ :=
  finiteKuboBastinSpectralChannelResponse system data
      (finiteDirectionalCurrentResponseChannel system geometry direction K q)
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
    finiteKuboBastinSpectralChannelResponse
    finiteDirectionalCurrentResponseChannel
    finiteKuboBastinSpectralVertexSum
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteKuboGreenwoodDirectionalCurrentTerm_eq_bastinSpectral
    system data geometry direction K q omega eta heta mn

end
end Transport
end Fermionic
end SecondQuantization

import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood
import LeanCondensedMatter.Transport.KuboBastin.Finite

set_option linter.style.header false

/-!
# Fermionic directional Kubo–Bastin spectral conductivity

The statistics-independent transition algebra lives in `Transport.KuboBastin.PurePoint`, while
finite spectral-index response sums live in `Transport.KuboBastin.Finite`. This module retains only
the finite-lattice directional electric-current specialization derived from Kubo–Greenwood.

The adiabatic switching rate `η` has units of inverse time, whereas the resolvent broadening has
units of energy. With the repository's explicit reduced Planck constant, the matching retarded
resolvent is

```text
Gᴿ(Eₘ + ℏω, ℏη) = ((Eₘ + ℏω + iℏη) I - H)⁻¹.
```

The Peierls contact contribution and finite-volume electric-field normalization remain explicit.
No zero-broadening, zero-frequency, thermodynamic, disorder, or trace-class statement is made.
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

/-- Finite regularized directional Kubo–Bastin conductivity in spectral resolvent form, with the
Peierls contact term retained explicitly. -/
noncomputable def finiteKuboBastinSpectralDirectionalConductivity
    [Fintype ι] (convention : QuantumTheory.Transport.PositiveVolume) : ℂ :=
  finiteKuboBastinSpectralVertexResponse system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
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
    finiteKuboBastinSpectralVertexResponse
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

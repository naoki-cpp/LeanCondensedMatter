import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood
import LeanCondensedMatter.Transport.KuboBastin.Finite

set_option linter.style.header false

/-!
# Fermionic Kubo–Bastin spectral conductivity components

The statistics-independent transition algebra lives in `Transport.KuboBastin.PurePoint`, while
finite spectral-index response sums live in `Transport.KuboBastin.Finite`. This module specializes
that neutral two-vertex response to finite-lattice electric-current conductivity components.

The first direction selects the measured current and the second selects the source field, so the
public component API represents `σ_ij`. The historical directional API is retained as the diagonal
specialization `i = j`.

The adiabatic switching rate `η` has units of inverse time, whereas the resolvent broadening has
units of energy. With the repository's explicit reduced Planck constant, the matching retarded
resolvent is

```text
Gᴿ(Eₘ + ℏω, ℏη) = ((Eₘ + ℏω + iℏη) I - H)⁻¹.
```

The mixed Peierls contact contribution and finite-volume electric-field normalization remain
explicit. No zero-broadening, zero-frequency, thermodynamic, disorder, or trace-class statement is
made.
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

/-- One finite Kubo–Bastin spectral transition for the conductivity component with current measured
along `measuredDirection` and source field along `sourceDirection`. -/
noncomputable def finiteKuboBastinSpectralCurrentComponentTerm
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) : ℂ :=
  purePointKuboBastinSpectralVertexTerm system data
    (boundedDirectionalCurrent geometry measuredDirection
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry sourceDirection
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta mn

/-- At positive switching rate, each Kubo–Greenwood conductivity-component term equals its
retarded-resolvent Kubo–Bastin spectral form. -/
theorem finiteKuboGreenwoodCurrentComponentTerm_eq_bastinSpectral
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (heta : 0 < eta) (mn : ι × ι) :
    finiteKuboGreenwoodCurrentComponentTerm
        system data geometry measuredDirection sourceDirection K q omega eta mn =
      finiteKuboBastinSpectralCurrentComponentTerm
        system data geometry measuredDirection sourceDirection K q omega eta mn := by
  simpa [finiteKuboGreenwoodCurrentComponentTerm,
    finiteKuboBastinSpectralCurrentComponentTerm] using
    purePointLehmannVertexTerm_eq_bastinSpectral system data
      (boundedDirectionalCurrent geometry measuredDirection
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry sourceDirection
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta heta mn

/-- Finite regularized Kubo–Bastin conductivity component `σ_ij` in spectral resolvent form. -/
noncomputable def finiteKuboBastinSpectralConductivityComponent
    [Fintype ι]
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (convention : QuantumTheory.Transport.PositiveVolume) : ℂ :=
  finiteKuboBastinSpectralVertexResponse system data
      (boundedDirectionalCurrent geometry measuredDirection
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry sourceDirection
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedMixedDirectionalContact geometry measuredDirection sourceDirection
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta *
    finiteVolumeConductivityNormalization convention omega eta

/-- The component Kubo–Bastin resolvent form is exactly the component Kubo–Greenwood expression at
positive switching rate. -/
theorem finiteKuboGreenwoodConductivityComponent_eq_bastinSpectral
    [Fintype ι]
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (convention : QuantumTheory.Transport.PositiveVolume) (heta : 0 < eta) :
    finiteKuboGreenwoodConductivityComponent
        convention system data geometry measuredDirection sourceDirection K q omega eta =
      finiteKuboBastinSpectralConductivityComponent
        system data geometry measuredDirection sourceDirection K q omega eta convention := by
  unfold finiteKuboGreenwoodConductivityComponent
    finiteKuboBastinSpectralConductivityComponent
    finiteKuboBastinSpectralVertexResponse
    finiteKuboBastinSpectralVertexSum
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteKuboGreenwoodCurrentComponentTerm_eq_bastinSpectral
    system data geometry measuredDirection sourceDirection K q omega eta heta mn

variable
  (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
  (K : LocallyFiniteHopping Site) (q omega eta : ℝ)

/-- One finite directional-current Kubo–Bastin spectral transition, the diagonal specialization of
the component response. -/
noncomputable def finiteKuboBastinSpectralDirectionalCurrentTerm
    (mn : ι × ι) : ℂ :=
  purePointKuboBastinSpectralVertexTerm system data
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta mn

/-- The component transition reduces definitionally to the directional transition when the measured
and source directions coincide. -/
@[simp]
theorem finiteKuboBastinSpectralCurrentComponentTerm_self
    (mn : ι × ι) :
    finiteKuboBastinSpectralCurrentComponentTerm
        system data geometry direction direction K q omega eta mn =
      finiteKuboBastinSpectralDirectionalCurrentTerm
        system data geometry direction K q omega eta mn := by
  rfl

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

/-- The diagonal component Kubo–Bastin API reproduces the historical directional conductivity. -/
@[simp]
theorem finiteKuboBastinSpectralConductivityComponent_self
    [Fintype ι] (convention : QuantumTheory.Transport.PositiveVolume) :
    finiteKuboBastinSpectralConductivityComponent
        system data geometry direction direction K q omega eta convention =
      finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention := by
  unfold finiteKuboBastinSpectralConductivityComponent
    finiteKuboBastinSpectralDirectionalConductivity
  rw [boundedMixedDirectionalContact_self]

/-- The finite spectral Kubo–Bastin resolvent form is exactly the finite Kubo–Greenwood directional
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

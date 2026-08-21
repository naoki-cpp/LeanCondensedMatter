import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood
import LeanCondensedMatter.Transport.FiniteKuboBastin

set_option linter.style.header false

/-!
# Fermionic directional Kubo–Bastin spectral conductivity

The statistics-independent pure-point resolvent and measured/source Kubo–Bastin machinery lives in
`Transport.FiniteKuboBastin`.  This module retains only the finite-lattice directional electric
current specialization derived from Kubo–Greenwood.

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

open Lattice
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
  -(((data.probability mn.1 - data.probability mn.2 : ℝ) : ℂ)) *
    inner ℂ (data.basis mn.1)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K (data.basis mn.2)) *
    inner ℂ (data.basis mn.2)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K (data.basis mn.1)) *
    inner ℂ (data.basis mn.2)
      (retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis mn.2))

/-- At positive switching rate, each directional Kubo–Greenwood term equals its retarded-resolvent
spectral form. -/
theorem finiteKuboGreenwoodDirectionalCurrentTerm_eq_bastinSpectral
    (heta : 0 < eta) (mn : ι × ι) :
    finiteKuboGreenwoodDirectionalCurrentTerm
        system data geometry direction K q omega eta mn =
      finiteKuboBastinSpectralDirectionalCurrentTerm
        system data geometry direction K q omega eta mn := by
  have hhbar : system.hbar ≠ 0 := ne_of_gt system.hbar_pos
  have hhbarComplex : (system.hbar : ℂ) ≠ 0 := by
    exact_mod_cast hhbar
  have hshift := retardedSpectralShift_ne_zero system.hbar omega eta
    (data.energy mn.1) (data.energy mn.2) system.hbar_pos heta
  unfold finiteKuboGreenwoodDirectionalCurrentTerm lehmannTerm
  rw [lehmannDenominator_eq_retardedSpectralShift
    system.hbar omega eta (data.energy mn.1) (data.energy mn.2) hhbar]
  unfold finiteKuboBastinSpectralDirectionalCurrentTerm
  rw [inner_purePointBasis_retardedResolvent system data omega eta heta mn.1 mn.2]
  unfold purePointTransitionWeight
  field_simp [hhbar, hhbarComplex, hshift]

/-- Finite regularized directional Kubo–Bastin conductivity in spectral resolvent form, with the
Peierls contact term retained explicitly. -/
noncomputable def finiteKuboBastinSpectralDirectionalConductivity
    [Fintype ι] (convention : QuantumTheory.Transport.PositiveVolume) : ℂ :=
  ((∑ mn : ι × ι,
      finiteKuboBastinSpectralDirectionalCurrentTerm
        system data geometry direction K q omega eta mn) +
      purePointNormalizedExpectation system data
        (boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K)) *
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

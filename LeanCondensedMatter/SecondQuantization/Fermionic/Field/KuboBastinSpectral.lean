import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboGreenwood
import LeanCondensedMatter.Transport.Resolvent

set_option linter.style.header false

/-!
# Finite resolvent spectral form of the Kubo conductivity

This module performs the first Kubo–Bastin rewrite of the finite Kubo–Greenwood conductivity.
The adiabatic switching rate `η` has units of inverse time, whereas the resolvent broadening has
units of energy. With the repository's explicit reduced Planck constant, the matching retarded
resolvent is therefore

```text
Gᴿ(Eₘ + ℏω, ℏη) = ((Eₘ + ℏω + iℏη) I - H)⁻¹.
```

The scalar Lehmann denominator obeys

```text
η - i(ω + (Eₘ-Eₙ)/ℏ)
  = (-i/ℏ) ((Eₘ + ℏω + iℏη) - Eₙ).
```

Consequently each finite Kubo–Greenwood transition is rewritten as a matrix element of the
retarded resolvent on the same energy eigenbasis. The contact contribution and the finite-volume
electric-field normalization remain unchanged and explicit.

This is a finite spectral resolvent representation, not yet the ordinary-trace packaging. No
zero-broadening, zero-frequency, thermodynamic, disorder, or trace-class statement is made.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open Lattice

open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Energy argument of the retarded resolvent associated with a transition whose first state has
energy `Eₘ`. -/
def kuboBastinRetardedEnergy (hbar omega energy : ℝ) : ℝ :=
  energy + hbar * omega

/-- Energy broadening matching the adiabatic switching rate. -/
def kuboBastinEnergyBroadening (hbar eta : ℝ) : ℝ :=
  hbar * eta

/-- Positive `ℏ` and positive switching rate give a positive resolvent energy broadening. -/
theorem kuboBastinEnergyBroadening_pos
    (hbar eta : ℝ) (hhbar : 0 < hbar) (heta : 0 < eta) :
    0 < kuboBastinEnergyBroadening hbar eta := by
  exact mul_pos hhbar heta

/-- The time-rate Lehmann denominator is the retarded energy denominator scaled by `-i/ℏ`. -/
theorem lehmannDenominator_eq_retardedSpectralShift
    (hbar omega eta energyₘ energyₙ : ℝ) (hhbar : hbar ≠ 0) :
    lehmannDenominator hbar omega eta (energyₘ - energyₙ) =
      (-(Complex.I) / (hbar : ℂ)) *
        (retardedSpectralParameter
            (kuboBastinRetardedEnergy hbar omega energyₘ)
            (kuboBastinEnergyBroadening hbar eta) -
          (energyₙ : ℂ)) := by
  apply Complex.ext
  · simp [lehmannDenominator, retardedSpectralParameter,
      kuboBastinRetardedEnergy, kuboBastinEnergyBroadening]
    field_simp [hhbar]
  · simp [lehmannDenominator, retardedSpectralParameter,
      kuboBastinRetardedEnergy, kuboBastinEnergyBroadening]
    field_simp [hhbar]
    ring

/-- The retarded spectral shift is nonzero at positive switching rate. -/
theorem retardedSpectralShift_ne_zero
    (hbar omega eta energyₘ energyₙ : ℝ)
    (hhbar : 0 < hbar) (heta : 0 < eta) :
    retardedSpectralParameter
          (kuboBastinRetardedEnergy hbar omega energyₘ)
          (kuboBastinEnergyBroadening hbar eta) -
        (energyₙ : ℂ) ≠ 0 := by
  intro hzero
  have him : hbar * eta = 0 := by
    have himZero := congrArg Complex.im hzero
    simpa [retardedSpectralParameter, kuboBastinEnergyBroadening] using himZero
  exact (mul_ne_zero (ne_of_gt hhbar) (ne_of_gt heta)) him

variable
  (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
  (data : PurePointLehmannData system ι)

/-- The retarded resolvent acts diagonally on the supplied energy eigenbasis. -/
theorem retardedResolvent_apply_purePointBasis
    (omega eta : ℝ) (heta : 0 < eta) (m n : ι) :
    retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis n) =
      (retardedSpectralParameter
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta) -
        (data.energy n : ℂ))⁻¹ • data.basis n := by
  let z := retardedSpectralParameter
    (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
    (kuboBastinEnergyBroadening system.hbar eta)
  let S : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
    algebraMap ℂ (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) z -
      system.hamiltonian.1
  let G := retardedResolvent system.hamiltonian.1
    (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
    (kuboBastinEnergyBroadening system.hbar eta)
  have hbroadening :
      0 < kuboBastinEnergyBroadening system.hbar eta :=
    kuboBastinEnergyBroadening_pos system.hbar eta system.hbar_pos heta
  have hSG : S * G = 1 := by
    simpa [S, G, z] using
      (retardedShift_mul_resolvent system.hamiltonian.1
        system.hamiltonian.2
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta) hbroadening)
  have hGS : G * S = 1 := by
    simpa [S, G, z] using
      (resolvent_mul_retardedShift system.hamiltonian.1
        system.hamiltonian.2
        (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
        (kuboBastinEnergyBroadening system.hbar eta) hbroadening)
  have hshift : z - (data.energy n : ℂ) ≠ 0 := by
    simpa [z] using
      (retardedSpectralShift_ne_zero system.hbar omega eta
        (data.energy m) (data.energy n) system.hbar_pos heta)
  have hS_basis : S (data.basis n) =
      (z - (data.energy n : ℂ)) • data.basis n := by
    simp [S, data.hamiltonian_apply_basis n, sub_smul]
  have hS_injective : Function.Injective S := by
    intro x y hxy
    calc
      x = (G * S) x := by rw [hGS]; simp
      _ = G (S x) := rfl
      _ = G (S y) := congrArg G hxy
      _ = (G * S) y := rfl
      _ = y := by rw [hGS]; simp
  apply hS_injective
  calc
    S (G (data.basis n)) = data.basis n := by
      change (S * G) (data.basis n) = data.basis n
      rw [hSG]
      simp
    _ = S ((z - (data.energy n : ℂ))⁻¹ • data.basis n) := by
      rw [map_smul, hS_basis]
      rw [← mul_smul]
      simp [hshift]

/-- The diagonal matrix element of the retarded resolvent is its scalar spectral denominator. -/
theorem inner_purePointBasis_retardedResolvent
    (omega eta : ℝ) (heta : 0 < eta) (m n : ι) :
    inner ℂ (data.basis n)
        (retardedResolvent system.hamiltonian.1
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta)
          (data.basis n)) =
      (retardedSpectralParameter
          (kuboBastinRetardedEnergy system.hbar omega (data.energy m))
          (kuboBastinEnergyBroadening system.hbar eta) -
        (data.energy n : ℂ))⁻¹ := by
  rw [retardedResolvent_apply_purePointBasis system data omega eta heta m n]
  rw [inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, data.basis.orthonormal.norm_eq_one]

variable [LinearOrder Site]
variable
  (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
  (K : LocallyFiniteHopping Site) (q omega eta : ℝ)

/-- One finite Kubo–Bastin spectral transition term written with the retarded resolvent from the
bounded transport layer. -/
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

/-- At positive switching rate, each Kubo–Greenwood term equals its retarded-resolvent spectral
form. -/
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

/-- Finite regularized Kubo–Bastin conductivity in spectral resolvent form, with the Peierls contact
term retained explicitly. -/
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
end Field
end Fermionic
end SecondQuantization

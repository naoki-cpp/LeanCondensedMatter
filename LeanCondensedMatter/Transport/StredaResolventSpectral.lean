import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import LeanCondensedMatter.Transport.Resolvent

set_option linter.style.header false

/-!
# Pure-point spectral action of the Středa resolvents

The static Středa energy integral evaluates retarded and advanced resolvents at an arbitrary real
integration energy. The earlier finite Kubo–Bastin spectral layer only needed a retarded resolvent
at the transition-dependent energy `Eₘ + ℏω`.

This module records the general pure-point action required by the energy-integral bridge. At every
strictly positive energy broadening, both resolvents and their squares act diagonally on the supplied
Hamiltonian eigenbasis with their explicit scalar denominators.

No trace, occupation integral, contact cancellation, zero-broadening limit, or conductivity claim
is made here.
-/

namespace QuantumTheory
namespace Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- The retarded resolvent acts diagonally on a pure-point energy basis at an arbitrary real
energy. -/
theorem retardedResolvent_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    retardedResolvent system.hamiltonian.1 energy broadening (data.basis n) =
      (retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ •
        data.basis n := by
  let z := retardedSpectralParameter energy broadening
  let S : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - system.hamiltonian.1
  let G : H →L[ℂ] H := retardedResolvent system.hamiltonian.1 energy broadening
  have hSG : S * G = 1 := by
    simpa [S, G, z] using
      retardedShift_mul_resolvent system.hamiltonian.1 system.hamiltonian.2
        energy broadening hbroadening
  have hGS : G * S = 1 := by
    simpa [S, G, z] using
      resolvent_mul_retardedShift system.hamiltonian.1 system.hamiltonian.2
        energy broadening hbroadening
  have hshift : z - (data.energy n : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [z, retardedSpectralParameter] at him
    linarith
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
      rw [map_smul, hS_basis, ← mul_smul]
      simp [hshift]

/-- The advanced resolvent acts diagonally on a pure-point energy basis at an arbitrary real
energy. -/
theorem advancedResolvent_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    advancedResolvent system.hamiltonian.1 energy broadening (data.basis n) =
      (advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ •
        data.basis n := by
  let z := advancedSpectralParameter energy broadening
  let S : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - system.hamiltonian.1
  let G : H →L[ℂ] H := advancedResolvent system.hamiltonian.1 energy broadening
  have hSG : S * G = 1 := by
    simpa [S, G, z] using
      advancedShift_mul_resolvent system.hamiltonian.1 system.hamiltonian.2
        energy broadening hbroadening
  have hGS : G * S = 1 := by
    simpa [S, G, z] using
      resolvent_mul_advancedShift system.hamiltonian.1 system.hamiltonian.2
        energy broadening hbroadening
  have hshift : z - (data.energy n : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [z, advancedSpectralParameter] at him
    linarith
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
      rw [map_smul, hS_basis, ← mul_smul]
      simp [hshift]

/-- The square of the retarded resolvent has the squared scalar denominator on the energy basis. -/
theorem retardedResolvent_sq_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    ((retardedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  rw [pow_two]
  change retardedResolvent system.hamiltonian.1 energy broadening
      (retardedResolvent system.hamiltonian.1 energy broadening (data.basis n)) = _
  rw [retardedResolvent_apply_purePointBasis_at_energy
    system data energy broadening hbroadening n]
  rw [map_smul]
  rw [retardedResolvent_apply_purePointBasis_at_energy
    system data energy broadening hbroadening n]
  rw [smul_smul, pow_two]

/-- The square of the advanced resolvent has the squared scalar denominator on the energy basis. -/
theorem advancedResolvent_sq_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    ((advancedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  rw [pow_two]
  change advancedResolvent system.hamiltonian.1 energy broadening
      (advancedResolvent system.hamiltonian.1 energy broadening (data.basis n)) = _
  rw [advancedResolvent_apply_purePointBasis_at_energy
    system data energy broadening hbroadening n]
  rw [map_smul]
  rw [advancedResolvent_apply_purePointBasis_at_energy
    system data energy broadening hbroadening n]
  rw [smul_smul, pow_two]

/-- Diagonal matrix element of the arbitrary-energy retarded resolvent. -/
theorem inner_purePointBasis_retardedResolvent_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    inner ℂ (data.basis n)
        (retardedResolvent system.hamiltonian.1 energy broadening (data.basis n)) =
      (retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ := by
  rw [retardedResolvent_apply_purePointBasis_at_energy
    system data energy broadening hbroadening n]
  rw [inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, data.basis.orthonormal.norm_eq_one]

/-- Diagonal matrix element of the arbitrary-energy advanced resolvent. -/
theorem inner_purePointBasis_advancedResolvent_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    inner ℂ (data.basis n)
        (advancedResolvent system.hamiltonian.1 energy broadening (data.basis n)) =
      (advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ := by
  rw [advancedResolvent_apply_purePointBasis_at_energy
    system data energy broadening hbroadening n]
  rw [inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, data.basis.orthonormal.norm_eq_one]

end
end Transport
end QuantumTheory

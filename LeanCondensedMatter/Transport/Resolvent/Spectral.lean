import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import LeanCondensedMatter.Transport.Resolvent

set_option linter.style.header false

/-!
# Spectral action of retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian, the retarded and advanced resolvents act diagonally on every
Hamiltonian eigenvector. This module owns that dimension-independent eigenvector theorem and derives
the pure-point Hilbert-basis formulas used by finite Kubo–Bastin and Středa spectral expansions.

The canonical core is stated for an arbitrary eigenvector rather than for `PurePointLehmannData`.
Pure-point basis formulas, squared-resolvent formulas, and diagonal matrix elements are corollaries.

No trace, occupation integral, contact cancellation, zero-broadening limit, or conductivity claim is
made here.
-/

namespace QuantumTheory
namespace Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The retarded resolvent acts on a Hamiltonian eigenvector by the corresponding scalar resolvent
factor. -/
theorem retardedResolvent_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy broadening v =
      (retardedSpectralParameter energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  let z := retardedSpectralParameter energy broadening
  let S : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - hamiltonian
  let G : H →L[ℂ] H := retardedResolvent hamiltonian energy broadening
  have hSG : S * G = 1 := by
    simpa [S, G, z] using
      retardedShift_mul_resolvent hamiltonian hself energy broadening hbroadening
  have hGS : G * S = 1 := by
    simpa [S, G, z] using
      resolvent_mul_retardedShift hamiltonian hself energy broadening hbroadening
  have hshift : z - (eigenvalue : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [z, retardedSpectralParameter] at him
    linarith
  have hS_v : S v = (z - (eigenvalue : ℂ)) • v := by
    change z • v - hamiltonian v = _
    rw [hv]
    exact (sub_smul z (eigenvalue : ℂ) v).symm
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
    S (G v) = v := by
      change (S * G) v = v
      rw [hSG]
      simp
    _ = S ((z - (eigenvalue : ℂ))⁻¹ • v) := by
      rw [map_smul, hS_v, ← mul_smul]
      simp [hshift]

/-- The advanced resolvent acts on a Hamiltonian eigenvector by the corresponding scalar resolvent
factor. -/
theorem advancedResolvent_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy broadening v =
      (advancedSpectralParameter energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  let z := advancedSpectralParameter energy broadening
  let S : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - hamiltonian
  let G : H →L[ℂ] H := advancedResolvent hamiltonian energy broadening
  have hSG : S * G = 1 := by
    simpa [S, G, z] using
      advancedShift_mul_resolvent hamiltonian hself energy broadening hbroadening
  have hGS : G * S = 1 := by
    simpa [S, G, z] using
      resolvent_mul_advancedShift hamiltonian hself energy broadening hbroadening
  have hshift : z - (eigenvalue : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [z, advancedSpectralParameter] at him
    linarith
  have hS_v : S v = (z - (eigenvalue : ℂ)) • v := by
    change z • v - hamiltonian v = _
    rw [hv]
    exact (sub_smul z (eigenvalue : ℂ) v).symm
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
    S (G v) = v := by
      change (S * G) v = v
      rw [hSG]
      simp
    _ = S ((z - (eigenvalue : ℂ))⁻¹ • v) := by
      rw [map_smul, hS_v, ← mul_smul]
      simp [hshift]

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
  exact retardedResolvent_apply_eigenvector
    system.hamiltonian.1 system.hamiltonian.2
    (data.hamiltonian_apply_basis n) energy broadening hbroadening

/-- The advanced resolvent acts diagonally on a pure-point energy basis at an arbitrary real
energy. -/
theorem advancedResolvent_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    advancedResolvent system.hamiltonian.1 energy broadening (data.basis n) =
      (advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ •
        data.basis n := by
  exact advancedResolvent_apply_eigenvector
    system.hamiltonian.1 system.hamiltonian.2
    (data.hamiltonian_apply_basis n) energy broadening hbroadening

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

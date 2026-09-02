import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Spectral action of retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian, the retarded and advanced resolvents act diagonally on every
Hamiltonian eigenvector. The representation-independent resolvent/eigenvector theorem is owned by
`Analysis.Operator.Spectral.Resolvent`; this module owns the side-indexed transport specialization
and its conventional retarded/advanced views.

No trace, occupation integral, contact cancellation, zero-broadening limit, or conductivity claim is
made here.
-/

namespace QuantumTheory
namespace Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A spectral resolvent on either side acts on a Hamiltonian eigenvector by the corresponding
scalar resolvent factor. -/
theorem spectralResolvent_apply_eigenvector
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    spectralResolvent side hamiltonian energy broadening v =
      (spectralParameter side energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  unfold spectralResolvent
  apply QuantumTheory.resolvent_apply_eigenvector
  · exact QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameter side energy broadening)
        (by
          rw [spectralParameter_im]
          exact mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)
  · exact spectralParameter_sub_real_ne_zero
      side energy broadening eigenvalue hbroadening
  · exact hv

/-- The retarded resolvent acts on a Hamiltonian eigenvector by the corresponding scalar resolvent
factor. -/
theorem retardedResolvent_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy broadening v =
      (retardedSpectralParameter energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  simpa only [spectralResolvent_retarded, spectralParameter_retarded] using
    spectralResolvent_apply_eigenvector
      .retarded hamiltonian hself hv energy broadening (ne_of_gt hbroadening)

/-- The advanced resolvent acts on a Hamiltonian eigenvector by the corresponding scalar resolvent
factor. -/
theorem advancedResolvent_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy broadening v =
      (advancedSpectralParameter energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  simpa only [spectralResolvent_advanced, spectralParameter_advanced] using
    spectralResolvent_apply_eigenvector
      .advanced hamiltonian hself hv energy broadening (ne_of_gt hbroadening)

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- Either spectral-side resolvent acts diagonally on a pure-point energy basis at an arbitrary real
energy. -/
theorem spectralResolvent_apply_purePointBasis_at_energy
    (side : SpectralSide)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (n : ι) :
    spectralResolvent side system.hamiltonian.1 energy broadening (data.basis n) =
      (spectralParameter side energy broadening - (data.energy n : ℂ))⁻¹ •
        data.basis n := by
  exact spectralResolvent_apply_eigenvector
    side system.hamiltonian.1 system.hamiltonian.2
    (data.hamiltonian_apply_basis n) energy broadening hbroadening

/-- The retarded resolvent acts diagonally on a pure-point energy basis at an arbitrary real
energy. -/
theorem retardedResolvent_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    retardedResolvent system.hamiltonian.1 energy broadening (data.basis n) =
      (retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ •
        data.basis n := by
  simpa only [spectralResolvent_retarded, spectralParameter_retarded] using
    spectralResolvent_apply_purePointBasis_at_energy
      system data .retarded energy broadening (ne_of_gt hbroadening) n

/-- The advanced resolvent acts diagonally on a pure-point energy basis at an arbitrary real
energy. -/
theorem advancedResolvent_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    advancedResolvent system.hamiltonian.1 energy broadening (data.basis n) =
      (advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹ •
        data.basis n := by
  simpa only [spectralResolvent_advanced, spectralParameter_advanced] using
    spectralResolvent_apply_purePointBasis_at_energy
      system data .advanced energy broadening (ne_of_gt hbroadening) n

/-- On a pure-point energy basis, the square of either spectral-side resolvent has the squared
scalar denominator. -/
theorem spectralResolvent_sq_apply_purePointBasis_at_energy
    (side : SpectralSide)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (n : ι) :
    ((spectralResolvent side system.hamiltonian.1 energy broadening) ^ 2)
        (data.basis n) =
      ((spectralParameter side energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  rw [pow_two]
  change spectralResolvent side system.hamiltonian.1 energy broadening
      (spectralResolvent side system.hamiltonian.1 energy broadening (data.basis n)) = _
  rw [spectralResolvent_apply_purePointBasis_at_energy
    system data side energy broadening hbroadening n]
  rw [map_smul]
  rw [spectralResolvent_apply_purePointBasis_at_energy
    system data side energy broadening hbroadening n]
  rw [smul_smul, pow_two]

/-- The square of the retarded resolvent has the squared scalar denominator on the energy basis. -/
theorem retardedResolvent_sq_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    ((retardedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  simpa only [spectralResolvent_retarded, spectralParameter_retarded] using
    spectralResolvent_sq_apply_purePointBasis_at_energy
      system data .retarded energy broadening (ne_of_gt hbroadening) n

/-- The square of the advanced resolvent has the squared scalar denominator on the energy basis. -/
theorem advancedResolvent_sq_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    ((advancedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  simpa only [spectralResolvent_advanced, spectralParameter_advanced] using
    spectralResolvent_sq_apply_purePointBasis_at_energy
      system data .advanced energy broadening (ne_of_gt hbroadening) n

end
end Transport
end QuantumTheory

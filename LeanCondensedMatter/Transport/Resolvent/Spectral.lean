import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Spectral action of regulated resolvents

For a bounded self-adjoint Hamiltonian, a resolvent at `E + iγ` with nonzero signed regulator acts
diagonally on every Hamiltonian eigenvector. The representation-independent resolvent/eigenvector
theorem is owned by `Analysis.Operator.Spectral.Resolvent`; this module owns the regulated and
pure-point transport specializations.

No trace, occupation integral, contact cancellation, zero-broadening limit, or conductivity claim is
made here.
-/

namespace QuantumTheory
namespace Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A resolvent with arbitrary nonzero signed regulator acts on a Hamiltonian eigenvector by the
corresponding scalar resolvent factor. -/
theorem resolvent_spectralParameterOfRegulator_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    resolvent hamiltonian (spectralParameterOfRegulator energy regulator) v =
      (spectralParameterOfRegulator energy regulator - (eigenvalue : ℂ))⁻¹ • v := by
  apply QuantumTheory.resolvent_apply_eigenvector
  · exact QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameterOfRegulator energy regulator)
        (by
          rw [spectralParameterOfRegulator_im]
          exact hregulator)
  · exact spectralParameterOfRegulator_sub_real_ne_zero
      energy regulator eigenvalue hregulator
  · exact hv

/-- A resolvent on either physical spectral side acts on a Hamiltonian eigenvector by the
corresponding scalar resolvent factor. -/
theorem resolvent_spectralParameter_apply_eigenvector
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    resolvent hamiltonian (spectralParameter side energy broadening) v =
      (spectralParameter side energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  simpa only [spectralParameter] using
    resolvent_spectralParameterOfRegulator_apply_eigenvector
      hamiltonian hself hv energy (side.sign * broadening)
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)

/-- The retarded resolvent acts on a Hamiltonian eigenvector by the corresponding scalar resolvent
factor. -/
theorem retardedResolvent_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy broadening v =
      (retardedSpectralParameter energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  simpa only [retardedResolvent, retardedSpectralParameter] using
    resolvent_spectralParameterOfRegulator_apply_eigenvector
      hamiltonian hself hv energy broadening (ne_of_gt hbroadening)

/-- The advanced resolvent acts on a Hamiltonian eigenvector by the corresponding scalar resolvent
factor. -/
theorem advancedResolvent_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy broadening v =
      (advancedSpectralParameter energy broadening - (eigenvalue : ℂ))⁻¹ • v := by
  simpa only [advancedResolvent, advancedSpectralParameter] using
    resolvent_spectralParameterOfRegulator_apply_eigenvector
      hamiltonian hself hv energy (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening))

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

/-- On a pure-point energy basis, the square of a resolvent with arbitrary nonzero signed regulator
has the squared scalar denominator. -/
theorem resolvent_spectralParameterOfRegulator_sq_apply_purePointBasis_at_energy
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (n : ι) :
    ((resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)) ^ 2)
        (data.basis n) =
      ((spectralParameterOfRegulator energy regulator - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  rw [pow_two]
  change resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)
      (resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)
        (data.basis n)) = _
  rw [resolvent_spectralParameterOfRegulator_apply_eigenvector
    system.hamiltonian.1 system.hamiltonian.2
    (data.hamiltonian_apply_basis n) energy regulator hregulator]
  rw [map_smul]
  rw [resolvent_spectralParameterOfRegulator_apply_eigenvector
    system.hamiltonian.1 system.hamiltonian.2
    (data.hamiltonian_apply_basis n) energy regulator hregulator]
  rw [smul_smul, pow_two]

/-- On a pure-point energy basis, the square of either physical spectral-side resolvent has the
squared scalar denominator. -/
theorem resolvent_spectralParameter_sq_apply_purePointBasis_at_energy
    (side : SpectralSide)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (n : ι) :
    ((resolvent system.hamiltonian.1 (spectralParameter side energy broadening)) ^ 2)
        (data.basis n) =
      ((spectralParameter side energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  simpa only [spectralParameter] using
    resolvent_spectralParameterOfRegulator_sq_apply_purePointBasis_at_energy
      system data energy (side.sign * broadening)
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening) n

/-- The square of the retarded resolvent has the squared scalar denominator on the energy basis. -/
theorem retardedResolvent_sq_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    ((retardedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((retardedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  simpa only [retardedResolvent, retardedSpectralParameter] using
    resolvent_spectralParameterOfRegulator_sq_apply_purePointBasis_at_energy
      system data energy broadening (ne_of_gt hbroadening) n

/-- The square of the advanced resolvent has the squared scalar denominator on the energy basis. -/
theorem advancedResolvent_sq_apply_purePointBasis_at_energy
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (n : ι) :
    ((advancedResolvent system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((advancedSpectralParameter energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  simpa only [advancedResolvent, advancedSpectralParameter] using
    resolvent_spectralParameterOfRegulator_sq_apply_purePointBasis_at_energy
      system data energy (-broadening) (neg_ne_zero.mpr (ne_of_gt hbroadening)) n

end
end Transport
end QuantumTheory

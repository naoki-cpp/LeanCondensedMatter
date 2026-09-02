import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Spectral action of regulated resolvents

For a bounded self-adjoint Hamiltonian, a resolvent at `E + iγ` with nonzero signed regulator acts
diagonally on every Hamiltonian eigenvector. The representation-independent resolvent/eigenvector
theorem is owned by `Analysis.Operator.Spectral.Resolvent`; this module owns the regulated and
pure-point transport specializations. Physical retarded/advanced branches are specialized locally by
consumers with `γ = ±η`.

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

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

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

end
end Transport
end QuantumTheory

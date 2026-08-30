import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Resolvent candidate uniqueness

This module keeps the retarded/advanced specialization of the generic resolvent-candidate uniqueness
argument owned by `Analysis.Operator.Spectral.Resolvent`. At a nonzero side-indexed broadening, the
physical spectral parameter lies outside the spectrum, so any candidate right inverse of the same
spectral shift equals the canonical resolvent.

The side-independent left-inverse/right-inverse algebra lives upstream in Analysis; model-specific
spectral projector and Pauli-basis consumers use the physical wrapper below.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A candidate right inverse of the side-indexed spectral shift equals the canonical resolvent. -/
theorem resolvent_eq_of_spectralShift_mul_eq_one
    (side : SpectralSide) (hamiltonian candidate : H →L[ℂ] H)
    (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (hleft :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
        candidate = 1) :
    resolvent hamiltonian (spectralParameter side energy broadening) = candidate := by
  apply QuantumTheory.resolvent_eq_of_spectralShift_mul_eq_one_of_not_mem
  · apply spectralParameter_not_mem_spectrum_of_im_ne_zero hamiltonian hself
    rw [spectralParameter_im]
    exact mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening
  · exact hleft

end
end Transport
end QuantumTheory

import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Regulated resolvent candidate uniqueness

This public transport-resolvent module specializes the generic resolvent-candidate uniqueness
argument owned by `Analysis.Operator.Spectral.Resolvent`. At a nonzero signed imaginary regulator,
the spectral parameter lies outside the spectrum of a self-adjoint Hamiltonian, so any candidate
right inverse of the same spectral shift equals the canonical resolvent.

The side-independent left-inverse/right-inverse algebra lives upstream in Analysis. Physical
retarded/advanced consumers specialize the signed regulator locally as `γ = ±η`.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A candidate right inverse of the spectral shift at an arbitrary nonzero signed regulator equals
the canonical resolvent. -/
theorem resolvent_eq_of_spectralShift_mul_eq_one
    (hamiltonian candidate : H →L[ℂ] H)
    (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0)
    (hleft :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) *
        candidate = 1) :
    resolvent hamiltonian (spectralParameterOfRegulator energy regulator) = candidate := by
  apply QuantumTheory.resolvent_eq_of_spectralShift_mul_eq_one_of_not_mem
  · apply QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero hamiltonian hself
    rw [spectralParameterOfRegulator_im]
    exact hregulator
  · exact hleft

end
end Transport
end QuantumTheory

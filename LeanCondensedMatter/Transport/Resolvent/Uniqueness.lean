import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Resolvent candidate uniqueness

Small algebraic helper for model-specific resolvent constructions.  At a nonzero side-indexed
broadening, the canonical resolvent is already a right inverse of the spectral shift.  Therefore
any candidate proved to be a left inverse of the same shift must equal that canonical resolvent.

Keeping this argument here avoids repeating the same left-inverse/right-inverse calculation in
spectral projector, Pauli-basis, and later model-specific resolvent consumers.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A candidate left inverse of the side-indexed spectral shift equals the canonical resolvent. -/
theorem resolvent_eq_of_spectralShift_mul_eq_one
    (side : SpectralSide) (hamiltonian candidate : H →L[ℂ] H)
    (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (hleft :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
        candidate = 1) :
    resolvent hamiltonian (spectralParameter side energy broadening) = candidate := by
  have hright := resolvent_mul_spectralShift
    side hamiltonian hself energy broadening hbroadening
  calc
    resolvent hamiltonian (spectralParameter side energy broadening) =
        resolvent hamiltonian (spectralParameter side energy broadening) * 1 := by simp
    _ = resolvent hamiltonian (spectralParameter side energy broadening) *
        ((algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
          candidate) := by rw [hleft]
    _ = (resolvent hamiltonian (spectralParameter side energy broadening) *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian)) *
          candidate := by rw [mul_assoc]
    _ = candidate := by rw [hright, one_mul]

end
end Transport
end QuantumTheory

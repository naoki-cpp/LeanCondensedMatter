import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.BornCommon
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Retarded finite-disorder Born self-energy

This module provides the conventional retarded physical name for the canonical side-indexed
first-Born self-energy owned by `Disorder.BornCommon`.

Second-order Born truncations, exact remainders, closure errors, and closure hypotheses remain
canonical `SpectralSide` objects in `BornCommon`; use their `.retarded` specialization directly
instead of introducing parallel retarded wrapper APIs here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Conventional retarded name for the canonical side-indexed first-Born self-energy. -/
noncomputable def bornRetardedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornSelfEnergy .retarded energy broadening

/-- The Born self-energy is the exact finite second moment with a clean retarded internal
propagator. -/
theorem bornRetardedSelfEnergy_eq_secondMoment
    (energy broadening : ℝ) :
    bornRetardedSelfEnergy ensemble energy broadening =
      ensemble.exactSecondMoment (ensemble.freeRetardedGreen energy broadening) := by
  rw [bornRetardedSelfEnergy, bornSelfEnergy_eq_secondMoment, freeGreen_retarded]

@[simp]
theorem bornSelfEnergy_retarded
    (energy broadening : ℝ) :
    ensemble.bornSelfEnergy .retarded energy broadening =
      ensemble.bornRetardedSelfEnergy energy broadening :=
  rfl

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

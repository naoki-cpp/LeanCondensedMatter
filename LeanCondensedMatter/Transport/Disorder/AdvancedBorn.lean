import LeanCondensedMatter.Transport.Disorder.BornCommon

set_option linter.style.header false

/-!
# Advanced finite-disorder Born self-energy

This module provides the conventional advanced physical name for the canonical side-indexed
first-Born self-energy owned by `Disorder.BornCommon`.

Second-order Born truncations, exact remainders, closure errors, and closure hypotheses remain
canonical `SpectralSide` objects in `BornCommon`; use their `.advanced` specialization directly
instead of introducing parallel advanced wrapper APIs here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Conventional advanced name for the canonical side-indexed first-Born self-energy. -/
noncomputable def bornAdvancedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornSelfEnergy .advanced energy broadening

/-- The advanced Born self-energy is the exact finite second moment with a clean advanced internal
propagator. -/
theorem bornAdvancedSelfEnergy_eq_secondMoment
    (energy broadening : ℝ) :
    bornAdvancedSelfEnergy ensemble energy broadening =
      ensemble.exactSecondMoment (ensemble.freeAdvancedGreen energy broadening) := by
  rw [bornAdvancedSelfEnergy, bornSelfEnergy_eq_secondMoment, freeGreen_advanced]

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

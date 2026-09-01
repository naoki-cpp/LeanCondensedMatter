import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Retarded finite-disorder Born self-energy

This module owns the conventional retarded first-Born self-energy for a finite disorder ensemble.
It is the exact finite second-moment action evaluated on the clean retarded Green operator; no
equality with the exact disorder-averaged self-energy or self-consistency is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Retarded first-Born self-energy: the exact finite second moment evaluated on the clean retarded
Green operator. -/
noncomputable def bornRetardedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeRetardedGreen energy broadening)

/-- The retarded Born self-energy is the exact finite second moment with a clean retarded internal
propagator. -/
theorem bornRetardedSelfEnergy_eq_secondMoment
    (energy broadening : ℝ) :
    bornRetardedSelfEnergy ensemble energy broadening =
      ensemble.exactSecondMoment (ensemble.freeRetardedGreen energy broadening) :=
  rfl

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

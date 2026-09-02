import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Finite-disorder Born self-energy

This module owns the conventional first-Born self-energy for a finite disorder ensemble. For either
spectral side, it is the exact finite second-moment action evaluated on the corresponding clean
Green operator. No equality with the exact disorder-averaged self-energy or self-consistency is
asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- First-Born self-energy on either spectral side: the exact finite second moment evaluated on the
corresponding clean Green operator. -/
noncomputable def bornSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeGreen side energy broadening)

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Shared finite-disorder Born self-energy

This module owns the side-indexed first-Born self-energy shared by the conventional retarded and
advanced specialization modules. The self-energy is the exact finite second moment evaluated on the
clean spectral-side Green operator.

No second-order Green truncation, closure hypothesis, self-consistency, Dyson-resummed Born Green
operator, vertex correction, Ward identity, trace-per-volume construction, or thermodynamic limit
is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Side-indexed first-Born self-energy: the exact finite second moment evaluated on the clean
spectral-side Green operator. This definition does not require centered disorder. -/
noncomputable def bornSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeGreen side energy broadening)

/-- The side-indexed Born self-energy is the exact finite second moment with the corresponding
clean spectral-side propagator. -/
theorem bornSelfEnergy_eq_secondMoment
    (side : SpectralSide) (energy broadening : ℝ) :
    ensemble.bornSelfEnergy side energy broadening =
      ensemble.exactSecondMoment (ensemble.freeGreen side energy broadening) :=
  rfl

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

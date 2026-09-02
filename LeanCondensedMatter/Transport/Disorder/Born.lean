import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Finite-disorder Born self-energy

This module owns the conventional first-Born self-energy for a finite disorder ensemble. The
analytic core is the exact finite second-moment action evaluated on the clean Green operator at an
arbitrary signed regulator `γ`; physical retarded/advanced branches specialize through
`γ = side.sign * η`.

No equality with the exact disorder-averaged self-energy or self-consistency is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- First-Born self-energy at an arbitrary signed regulator: the exact finite second moment applied
to the corresponding clean Green operator. -/
noncomputable def bornSelfEnergyOfRegulator
    (energy regulator : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeGreenOfRegulator energy regulator)

/-- First-Born self-energy on a physical spectral side. -/
noncomputable def bornSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornSelfEnergyOfRegulator energy (side.sign * broadening)

/-- Adjointing the first-Born self-energy reverses the signed regulator. -/
theorem star_bornSelfEnergyOfRegulator
    (energy regulator : ℝ) :
    star (ensemble.bornSelfEnergyOfRegulator energy regulator) =
      ensemble.bornSelfEnergyOfRegulator energy (-regulator) := by
  unfold bornSelfEnergyOfRegulator
  calc
    star (ensemble.exactSecondMoment (ensemble.freeGreenOfRegulator energy regulator)) =
        ensemble.exactSecondMoment (star (ensemble.freeGreenOfRegulator energy regulator)) :=
      (ensemble.exactSecondMoment_star
        (ensemble.freeGreenOfRegulator energy regulator)).symm
    _ = ensemble.exactSecondMoment (ensemble.freeGreenOfRegulator energy (-regulator)) := by
      apply congrArg ensemble.exactSecondMoment
      unfold freeGreenOfRegulator
      exact star_resolvent_spectralParameterOfRegulator
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

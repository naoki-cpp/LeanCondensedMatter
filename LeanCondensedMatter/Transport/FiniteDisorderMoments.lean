import LeanCondensedMatter.Transport.FiniteDisorder

set_option linter.style.header false

/-!
# Shared finite-disorder moment data

This module owns the centered finite second-moment data shared by retarded and advanced first-Born
transport approximations. The data depend only on the exact finite disorder ensemble and its exact
operator average; no resolvent, Born closure, self-consistency, or thermodynamic-limit structure is
introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Explicit centered-disorder and covariance assumptions for a finite ensemble. The covariance is
an operator-valued action on a supplied kernel; its exact finite second-moment realization is stored
as a field. -/
structure FiniteDisorderMomentData where
  /-- Operator-valued covariance action on an inserted bounded kernel. -/
  covariance : (H →L[ℂ] H) → H →L[ℂ] H
  /-- Exact centering condition `E[Vω] = 0`. -/
  centered :
    ensemble.operatorAverage (fun ω => (ensemble.impurityPotential ω).1) = 0
  /-- Identification of the covariance action with the exact weighted finite second moment. -/
  covariance_eq_secondMoment : ∀ kernel,
    covariance kernel =
      ensemble.operatorAverage (fun ω =>
        (ensemble.impurityPotential ω).1 * kernel *
          (ensemble.impurityPotential ω).1)

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

import LeanCondensedMatter.Transport.Disorder.Finite

set_option linter.style.header false

/-!
# Exact finite-disorder moments and centering data

This module owns the exact finite second-moment action shared by Born and SCBA transport
approximations, together with the explicit centering assumption used by first-Born averaging.
The exact second moment is computed directly from the finite disorder ensemble rather than supplied
as separate covariance data.

No resolvent, Born closure, self-consistency, or thermodynamic-limit structure is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Exact normalized finite second-moment action `E[Vω X Vω]` on a bounded operator `X`.
This is exact finite-ensemble data and carries no Born or self-consistency approximation. -/
noncomputable def exactSecondMoment
    (kernel : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    (ensemble.impurityPotential ω).1 * kernel *
      (ensemble.impurityPotential ω).1)

/-- Explicit centering assumption for a finite disorder ensemble. The exact second moment itself is
computed canonically by `FiniteDisorderEnsemble.exactSecondMoment`. -/
structure FiniteDisorderMomentData where
  /-- Exact centering condition `E[Vω] = 0`. -/
  centered :
    ensemble.operatorAverage (fun ω => (ensemble.impurityPotential ω).1) = 0

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

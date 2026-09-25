import LeanCondensedMatter.Transport.Disorder.Finite
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Normed.Operator.Mul

set_option linter.style.header false

/-!
# Exact finite-disorder moments and centering

This module owns the exact finite second-moment action shared by Born and SCBA transport
approximations, together with the explicit centering property used by first-Born averaging.
The second moment is constructed canonically as a bounded complex-linear operator on bounded
operators; its finite-average formula and adjoint compatibility are theorems rather than supplied
data.

No resolvent, Born closure, self-consistency, or thermodynamic-limit structure is introduced here.
-/

namespace QuantumTheory
namespace Transport

open scoped BigOperators

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Exact normalized finite second-moment action `X ↦ E[Vω X Vω]`, represented canonically as a
bounded complex-linear map on bounded operators. This is exact finite-ensemble data and carries no
Born or self-consistency approximation. -/
noncomputable def exactSecondMomentCLM :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ∑ ω,
    (ensemble.probability ω : ℂ) •
      ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H))
        (ensemble.impurityPotential ω).1
        (ensemble.impurityPotential ω).1)

/-- Exact normalized finite second moment `E[Vω X Vω]` of one bounded operator `X`. -/
noncomputable def exactSecondMoment
    (kernel : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.exactSecondMomentCLM kernel

/-- Weighted second moment `E[uω²]` of a supplied real scalar impurity amplitude. -/
noncomputable def scalarSecondMomentStrength (amplitude : Ω → ℝ) : ℂ :=
  ∑ ω, (ensemble.probability ω : ℂ) * (amplitude ω : ℂ) ^ 2

/-- The canonical exact second moment is the normalized finite operator average `E[Vω X Vω]`. -/
theorem exactSecondMoment_eq_operatorAverage
    (kernel : H →L[ℂ] H) :
    ensemble.exactSecondMoment kernel =
      ensemble.operatorAverage (fun ω =>
        (ensemble.impurityPotential ω).1 * kernel *
          (ensemble.impurityPotential ω).1) := by
  unfold exactSecondMoment exactSecondMomentCLM operatorAverage
  simp

/-- If every impurity potential is scalar, `Vω = uω I`, the exact second-moment action is scalar
multiplication by `E[uω²]`. -/
theorem exactSecondMoment_eq_scalarSecondMomentStrength_smul
    (amplitude : Ω → ℝ)
    (hscalar : ∀ ω,
      (ensemble.impurityPotential ω).1 =
        (amplitude ω : ℂ) • (1 : H →L[ℂ] H))
    (kernel : H →L[ℂ] H) :
    ensemble.exactSecondMoment kernel =
      ensemble.scalarSecondMomentStrength amplitude • kernel := by
  rw [ensemble.exactSecondMoment_eq_operatorAverage]
  unfold operatorAverage scalarSecondMomentStrength
  change
    (∑ ω, (ensemble.probability ω : ℂ) •
      ((ensemble.impurityPotential ω).1 * kernel *
        (ensemble.impurityPotential ω).1)) =
      (∑ ω, (ensemble.probability ω : ℂ) * (amplitude ω : ℂ) ^ 2) • kernel
  calc
    (∑ ω, (ensemble.probability ω : ℂ) •
      ((ensemble.impurityPotential ω).1 * kernel *
        (ensemble.impurityPotential ω).1)) =
        ∑ ω, ((ensemble.probability ω : ℂ) * (amplitude ω : ℂ) ^ 2) • kernel := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [hscalar ω]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, pow_two]
    _ = (∑ ω, (ensemble.probability ω : ℂ) * (amplitude ω : ℂ) ^ 2) • kernel := by
      rw [← Finset.sum_smul]

/-- The exact second-moment action preserves subtraction because its canonical realization is
complex-linear. -/
theorem exactSecondMoment_sub
    (left right : H →L[ℂ] H) :
    ensemble.exactSecondMoment (left - right) =
      ensemble.exactSecondMoment left - ensemble.exactSecondMoment right := by
  simpa only [exactSecondMoment] using
    ensemble.exactSecondMomentCLM.map_sub left right

/-- The exact second-moment action preserves adjoints because every impurity potential is
self-adjoint and every ensemble weight is real. -/
theorem exactSecondMoment_star
    (kernel : H →L[ℂ] H) :
    ensemble.exactSecondMoment (star kernel) =
      star (ensemble.exactSecondMoment kernel) := by
  rw [exactSecondMoment_eq_operatorAverage, exactSecondMoment_eq_operatorAverage]
  unfold operatorAverage
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro ω _
  simp [star_mul, (ensemble.impurityPotential ω).2.star_eq, mul_assoc]

/-- Right equivariance of the exact second moment. If every impurity potential commutes with a
bounded operator, that operator can be moved through the right side of the second-moment action. -/
theorem exactSecondMoment_mul_of_commutes
    (kernel right : H →L[ℂ] H)
    (hcommute : ∀ ω, Commute (ensemble.impurityPotential ω).1 right) :
    ensemble.exactSecondMoment kernel * right =
      ensemble.exactSecondMoment (kernel * right) := by
  rw [ensemble.exactSecondMoment_eq_operatorAverage,
    ensemble.exactSecondMoment_eq_operatorAverage]
  unfold operatorAverage
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_mul_assoc]
  apply congrArg (fun operator : H →L[ℂ] H => (ensemble.probability ω : ℂ) • operator)
  calc
    ((ensemble.impurityPotential ω).1 * kernel *
        (ensemble.impurityPotential ω).1) * right =
      (ensemble.impurityPotential ω).1 * kernel *
        ((ensemble.impurityPotential ω).1 * right) := by
          rw [mul_assoc]
    _ = (ensemble.impurityPotential ω).1 * kernel *
        (right * (ensemble.impurityPotential ω).1) := by
          rw [(hcommute ω).eq]
    _ = (ensemble.impurityPotential ω).1 * (kernel * right) *
        (ensemble.impurityPotential ω).1 := by
          simp only [mul_assoc]

/-- Left equivariance of the exact second moment. If every impurity potential commutes with a
bounded operator, that operator can be moved through the left side of the second-moment action. -/
theorem mul_exactSecondMoment_of_commutes
    (left kernel : H →L[ℂ] H)
    (hcommute : ∀ ω, Commute (ensemble.impurityPotential ω).1 left) :
    left * ensemble.exactSecondMoment kernel =
      ensemble.exactSecondMoment (left * kernel) := by
  rw [ensemble.exactSecondMoment_eq_operatorAverage,
    ensemble.exactSecondMoment_eq_operatorAverage]
  unfold operatorAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [mul_smul_comm]
  apply congrArg (fun operator : H →L[ℂ] H => (ensemble.probability ω : ℂ) • operator)
  calc
    left * ((ensemble.impurityPotential ω).1 * kernel *
        (ensemble.impurityPotential ω).1) =
      (left * (ensemble.impurityPotential ω).1) * kernel *
        (ensemble.impurityPotential ω).1 := by
          simp only [mul_assoc]
    _ = ((ensemble.impurityPotential ω).1 * left) * kernel *
        (ensemble.impurityPotential ω).1 := by
          rw [← (hcommute ω).eq]
    _ = (ensemble.impurityPotential ω).1 * (left * kernel) *
        (ensemble.impurityPotential ω).1 := by
          simp only [mul_assoc]

/-- Exact centered-disorder property `E[Vω] = 0`. The second moment is computed canonically and is
not stored as additional data. -/
def IsCentered : Prop :=
  ensemble.operatorAverage (fun ω => (ensemble.impurityPotential ω).1) = 0

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

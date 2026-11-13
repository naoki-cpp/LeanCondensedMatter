import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormCast

set_option linter.style.header false

/-!
# Exact two-particle insertions in a finite disorder ensemble

Averaging a product of two configuration-dependent Green operators is not the same as multiplying
their averages. This module isolates that distinction without invoking a Born, non-crossing,
Gaussian, or thermodynamic-limit approximation.

For any two operator families `Aω`, `Bω` and fixed insertion `J`, the exact identity is

```text
E[Aω J Bω] = E[Aω] J E[Bω]
           + E[(Aω - E[A]) J (Bω - E[B])].
```

The second term is a connected disorder insertion, not a diffuson or a resummed ladder.
Retarded/advanced applications are obtained from the signed-regulator Green functions; neither
an on-shell limit nor an impurity-diagrammatic closure follows from this algebra.
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

/-- Finite operator averaging preserves addition. -/
theorem operatorAverage_add
    (left right : Ω → H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => left ω + right ω) =
      ensemble.operatorAverage left + ensemble.operatorAverage right := by
  unfold operatorAverage
  simp only [smul_add, Finset.sum_add_distrib]

/-- Finite operator averaging preserves subtraction. -/
theorem operatorAverage_sub
    (left right : Ω → H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => left ω - right ω) =
      ensemble.operatorAverage left - ensemble.operatorAverage right := by
  unfold operatorAverage
  simp only [smul_sub, Finset.sum_sub_distrib]

/-- A constant operator is unchanged by a normalized disorder average. -/
@[simp]
theorem operatorAverage_const
    (operator : H →L[ℂ] H) :
    ensemble.operatorAverage (fun _ => operator) = operator := by
  unfold operatorAverage
  rw [← Finset.sum_smul]
  have hsum : (∑ ω, (ensemble.probability ω : ℂ)) = 1 := by
    exact_mod_cast ensemble.probability_sum
  simp [hsum]

/-- A fixed operator can be factored out on the right of a finite disorder average. -/
theorem operatorAverage_mul_right
    (operator : Ω → H →L[ℂ] H) (right : H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => operator ω * right) =
      ensemble.operatorAverage operator * right := by
  unfold operatorAverage
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_mul_assoc]

/-- A fixed operator can be factored out on the left of a finite disorder average. -/
theorem operatorAverage_mul_left
    (left : H →L[ℂ] H) (operator : Ω → H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => left * operator ω) =
      left * ensemble.operatorAverage operator := by
  unfold operatorAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [mul_smul_comm]

/-- Exact disorder average of a two-operator insertion with a fixed middle vertex. -/
noncomputable def averagedOperatorInsertion
    (left right : Ω → H →L[ℂ] H) (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω => left ω * vertex * right ω)

/-- Connected disorder insertion, centered separately in both operator factors. -/
noncomputable def connectedOperatorInsertion
    (left right : Ω → H →L[ℂ] H) (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    (left ω - ensemble.operatorAverage left) * vertex *
      (right ω - ensemble.operatorAverage right))

/-- Exact two-particle decomposition. The correction is the covariance of the two operator
families, with their noncommutative order and the middle vertex preserved. -/
theorem averagedOperatorInsertion_eq_mean_add_connected
    (left right : Ω → H →L[ℂ] H) (vertex : H →L[ℂ] H) :
    ensemble.averagedOperatorInsertion left right vertex =
      ensemble.operatorAverage left * vertex * ensemble.operatorAverage right +
        ensemble.connectedOperatorInsertion left right vertex := by
  let meanLeft : H →L[ℂ] H := ensemble.operatorAverage left
  let meanRight : H →L[ℂ] H := ensemble.operatorAverage right
  have hpoint (ω : Ω) :
      (left ω - meanLeft) * vertex * (right ω - meanRight) =
        left ω * vertex * right ω -
          left ω * (vertex * meanRight) -
          (meanLeft * vertex) * right ω +
          meanLeft * vertex * meanRight := by
    noncomm_ring
  have hconnected :
      ensemble.connectedOperatorInsertion left right vertex =
        ensemble.averagedOperatorInsertion left right vertex -
          meanLeft * vertex * meanRight := by
    calc
      ensemble.connectedOperatorInsertion left right vertex =
          ensemble.operatorAverage (fun ω =>
            left ω * vertex * right ω -
              left ω * (vertex * meanRight) -
              (meanLeft * vertex) * right ω +
              meanLeft * vertex * meanRight) := by
        change ensemble.operatorAverage (fun ω =>
          (left ω - meanLeft) * vertex * (right ω - meanRight)) = _
        apply congrArg ensemble.operatorAverage
        funext ω
        exact hpoint ω
      _ = ensemble.averagedOperatorInsertion left right vertex -
          meanLeft * vertex * meanRight := by
        rw [ensemble.operatorAverage_add, ensemble.operatorAverage_sub,
          ensemble.operatorAverage_sub,
          ensemble.operatorAverage_mul_right,
          ensemble.operatorAverage_mul_left,
          ensemble.operatorAverage_const]
        change ensemble.averagedOperatorInsertion left right vertex -
          meanLeft * (vertex * meanRight) -
          (meanLeft * vertex) * meanRight +
          meanLeft * vertex * meanRight =
            ensemble.averagedOperatorInsertion left right vertex -
              meanLeft * vertex * meanRight
        noncomm_ring
  rw [hconnected]
  change ensemble.averagedOperatorInsertion left right vertex =
    meanLeft * vertex * meanRight +
      (ensemble.averagedOperatorInsertion left right vertex -
        meanLeft * vertex * meanRight)
  abel

/-- Exact two-Green insertion at independently supplied energies and signed regulators. -/
noncomputable def averagedTwoGreenInsertionOfRegulators
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.averagedOperatorInsertion
    (fun ω => ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω)
    (fun ω => ensemble.configurationGreenOfRegulator energyRight regulatorRight ω)
    vertex

/-- Exact connected two-Green insertion (disorder covariance), not a ladder approximation. -/
noncomputable def connectedTwoGreenInsertionOfRegulators
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.connectedOperatorInsertion
    (fun ω => ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω)
    (fun ω => ensemble.configurationGreenOfRegulator energyRight regulatorRight ω)
    vertex

/-- The exact two-Green disorder average differs from the product of averaged Green operators
by the connected two-Green insertion. This is valid before any Born or ladder truncation. -/
theorem averagedTwoGreenInsertionOfRegulators_eq_mean_add_connected
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (vertex : H →L[ℂ] H) :
    ensemble.averagedTwoGreenInsertionOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex =
      ensemble.averagedGreenOfRegulator energyLeft regulatorLeft *
          vertex * ensemble.averagedGreenOfRegulator energyRight regulatorRight +
        ensemble.connectedTwoGreenInsertionOfRegulators
          energyLeft regulatorLeft energyRight regulatorRight vertex := by
  simpa only [averagedTwoGreenInsertionOfRegulators,
    connectedTwoGreenInsertionOfRegulators, averagedGreenOfRegulator] using
    ensemble.averagedOperatorInsertion_eq_mean_add_connected
      (fun ω => ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω)
      (fun ω => ensemble.configurationGreenOfRegulator energyRight regulatorRight ω)
      vertex

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory

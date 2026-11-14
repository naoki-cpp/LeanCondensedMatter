import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

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

/-- Exact disorder average of a two-operator insertion with a fixed middle vertex. -/
noncomputable def averagedOperatorInsertion
    (left right : Ω → H →L[ℂ] H) (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.average (fun ω => left ω * vertex * right ω)

/-- Connected disorder insertion, centered separately in both operator factors. -/
noncomputable def connectedOperatorInsertion
    (left right : Ω → H →L[ℂ] H) (vertex : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.average (fun ω =>
    (left ω - ensemble.average left) * vertex *
      (right ω - ensemble.average right))

/-- Exact two-particle decomposition. The correction is the covariance of the two operator
families, with their noncommutative order and the middle vertex preserved. -/
theorem averagedOperatorInsertion_eq_mean_add_connected
    (left right : Ω → H →L[ℂ] H) (vertex : H →L[ℂ] H) :
    ensemble.averagedOperatorInsertion left right vertex =
      ensemble.average left * vertex * ensemble.average right +
        ensemble.connectedOperatorInsertion left right vertex := by
  let meanLeft : H →L[ℂ] H := ensemble.average left
  let meanRight : H →L[ℂ] H := ensemble.average right
  have hpoint (ω : Ω) :
      (left ω - meanLeft) * vertex * (right ω - meanRight) =
        left ω * vertex * right ω -
          left ω * (vertex * meanRight) -
          (meanLeft * vertex) * right ω +
          meanLeft * vertex * meanRight := by
    noncomm_ring
  have hright :
      ensemble.average (fun ω => left ω * (vertex * meanRight)) =
        ensemble.average left * (vertex * meanRight) := by
    simpa using (ensemble.map_average
      ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H) 1 (vertex * meanRight)).toLinearMap)
      left).symm
  have hleft :
      ensemble.average (fun ω => (meanLeft * vertex) * right ω) =
        (meanLeft * vertex) * ensemble.average right := by
    simpa using (ensemble.map_average
      ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H) (meanLeft * vertex) 1).toLinearMap)
      right).symm
  have hconnected :
      ensemble.connectedOperatorInsertion left right vertex =
        ensemble.averagedOperatorInsertion left right vertex -
          meanLeft * vertex * meanRight := by
    calc
      ensemble.connectedOperatorInsertion left right vertex =
          ensemble.average (fun ω =>
            left ω * vertex * right ω -
              left ω * (vertex * meanRight) -
              (meanLeft * vertex) * right ω +
              meanLeft * vertex * meanRight) := by
        change ensemble.average (fun ω =>
          (left ω - meanLeft) * vertex * (right ω - meanRight)) = _
        apply congrArg ensemble.average
        funext ω
        exact hpoint ω
      _ = ensemble.averagedOperatorInsertion left right vertex -
          meanLeft * vertex * meanRight := by
        change ensemble.average
          ((fun ω => left ω * vertex * right ω) -
            (fun ω => left ω * (vertex * meanRight)) -
            (fun ω => (meanLeft * vertex) * right ω) +
            (fun _ => meanLeft * vertex * meanRight)) = _
        rw [map_add, map_sub, map_sub, hright, hleft, ensemble.average_const]
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

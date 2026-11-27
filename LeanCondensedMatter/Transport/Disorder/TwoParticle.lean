import LeanCondensedMatter.Analysis.Algebra.FiniteAverage
import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Algebra.Algebra.Bilinear

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
  let B : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
    (LinearMap.mul ℂ (H →L[ℂ] H)).comp
      ((LinearMap.mul ℂ (H →L[ℂ] H)).flip vertex)
  exact LinearMap.finiteWeightedSum_bilinear_eq_mean_add_centered
    (fun ω => (ensemble.probability ω : ℂ)) ensemble.probability_sum_complex B left right

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

import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Basic

set_option linter.style.header false

/-!
# Quenched connected correlations in a finite disorder ensemble

Each configuration supplies its own normalized expectation before disorder averaging.
The minimal expectation interface assumes normalization and linearity, not positivity;
physical density-state constructions can supply stronger hypotheses.

The connected product is `⟨A B⟩ω - ⟨A⟩ω ⟨B⟩ω`. Subtracting the product of
disorder-averaged one-point expectations instead differs by their disorder covariance.
No Gaussian law, Wick factorization, linked-cluster expansion, or analytic continuation is assumed.
-/

namespace QuantumTheory.Transport.FiniteDisorderEnsemble

open scoped BigOperators
open QuantumTheory.LinearResponse

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype Ω]

/-- Average the connected product after taking the supplied expectation in each configuration. -/
noncomputable def averagedConnectedCorrelation
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (expectation : Ω → NormalizedExpectation H) (A B : H →L[ℂ] H) : ℂ :=
  ensemble.average (fun ω => expectation ω (A * B) - expectation ω A * expectation ω B)

/-- The disconnected product remains inside the disorder average. -/
theorem averagedConnectedCorrelation_eq_average_sub
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (expectation : Ω → NormalizedExpectation H) (A B : H →L[ℂ] H) :
    ensemble.averagedConnectedCorrelation expectation A B =
      ensemble.average (fun ω => expectation ω (A * B)) -
        ensemble.average (fun ω => expectation ω A * expectation ω B) := by
  exact map_sub ensemble.average _ _

/-- The connected correlation of averaged one-point functions differs by disorder covariance. -/
theorem averagedConnectedCorrelation_eq_annealed_sub_covariance
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (expectation : Ω → NormalizedExpectation H) (A B : H →L[ℂ] H) :
    ensemble.averagedConnectedCorrelation expectation A B =
      (ensemble.average (fun ω => expectation ω (A * B)) -
        ensemble.average (fun ω => expectation ω A) *
          ensemble.average (fun ω => expectation ω B)) -
      (ensemble.average (fun ω => expectation ω A * expectation ω B) -
        ensemble.average (fun ω => expectation ω A) *
          ensemble.average (fun ω => expectation ω B)) := by
  rw [averagedConnectedCorrelation_eq_average_sub]
  ring

/-- A supplied configuration-wise four-leg expansion commutes with finite averaging.
The expansion is a required hypothesis, not a consequence of the ensemble interface. -/
theorem averagedConnectedCorrelation_eq_fourLegAverage
    {α : Type*} [Fintype α]
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (expectation : Ω → NormalizedExpectation H) (A B : H →L[ℂ] H)
    (coefficient : α → ℂ) (fourLeg : Ω → α → ℂ)
    (hfourLeg : ∀ ω, expectation ω (A * B) =
      ∑ a : α, coefficient a * fourLeg ω a) :
    ensemble.averagedConnectedCorrelation expectation A B =
      (∑ a : α, coefficient a * ensemble.average (fun ω => fourLeg ω a)) -
        ensemble.average (fun ω => expectation ω A * expectation ω B) := by
  rw [averagedConnectedCorrelation_eq_average_sub]
  congr 1
  calc
    ensemble.average (fun ω => expectation ω (A * B)) =
        ensemble.average (∑ a : α, coefficient a • (fun ω => fourLeg ω a)) := by
      apply ensemble.average_congr
      intro ω
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hfourLeg ω
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

end
end QuantumTheory.Transport.FiniteDisorderEnsemble

import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExponential
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonTrace
import Mathlib.Analysis.Analytic.Basic

set_option linter.style.header false

/-!
# Analytic finite-configuration Dyson partition function

For a finite configuration type, a basis-diagonal free energy, and an arbitrary interaction,
the interacting partition function is the finite-dimensional trace
`Tr exp(-β (H₀ + λV))`. Its Taylor coefficients are the statistics-independent
`dysonTraceCoeff` values.

Particle-specific perturbation theories should specialize this Common construction rather than
rebuild the analytic partition-function layer.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*} [Fintype Config]

/-- The finite-dimensional interacting partition function `Tr exp(-β (H₀ + λV))`. -/
noncomputable def analyticDysonPartitionFunction (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) : ℂ :=
  finiteOperatorTrace
    (NormedSpace.exp ((-β) • continuousInteractingHamiltonian energy V lam))

/-- The analytic partition function is the thermal trace of the interaction-picture Dyson
operator. -/
theorem analyticDysonPartitionFunction_eq_trace_dysonEvolution
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    analyticDysonPartitionFunction energy β V lam =
      finiteOperatorTrace
        ((continuousDiagonalEvolution energy (-β)).comp
          (Dyson.evolution (continuousInteractionPicture energy V) lam β)) := by
  unfold analyticDysonPartitionFunction
  apply congrArg finiteOperatorTrace
  change NormedSpace.exp ((-β) • continuousInteractingHamiltonian energy V lam) =
    continuousDiagonalEvolution energy (-β) *
      Dyson.evolution (continuousInteractionPicture energy V) lam β
  exact (continuousDiagonalEvolution_neg_mul_dysonEvolution_eq_exp
    energy V hβ lam).symm

/-- The Common Dyson trace coefficients sum to the interacting partition function. -/
theorem hasSum_dysonTraceCoeff_analyticDysonPartitionFunction
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) :
    HasSum
      (fun n : ℕ => lam ^ n * dysonTraceCoeff energy β V n)
      (analyticDysonPartitionFunction energy β V lam) := by
  rw [analyticDysonPartitionFunction_eq_trace_dysonEvolution energy hβ V lam]
  exact hasSum_dysonTraceCoeff energy hβ V lam

/-- The one-variable formal multilinear series of Common Dyson trace coefficients. -/
noncomputable def dysonTraceFPowerSeries (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (dysonTraceCoeff energy β V)

@[simp]
theorem coeff_dysonTraceFPowerSeries (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    (dysonTraceFPowerSeries energy β V).coeff n = dysonTraceCoeff energy β V n := by
  simp [dysonTraceFPowerSeries]

private theorem radius_dysonTraceFPowerSeries_eq_top
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    (dysonTraceFPowerSeries energy β V).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs : Summable (fun n : ℕ =>
      ‖(r : ℂ) ^ n * dysonTraceCoeff energy β V n‖) :=
    (hasSum_dysonTraceCoeff_analyticDysonPartitionFunction
      energy hβ V (r : ℂ)).summable.norm
  simpa [dysonTraceFPowerSeries, norm_mul, norm_pow, mul_comm] using hs

private theorem hasFPowerSeriesOnBall_analyticDysonPartitionFunction
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    HasFPowerSeriesOnBall (analyticDysonPartitionFunction energy β V)
      (dysonTraceFPowerSeries energy β V) 0 ⊤ := by
  refine ⟨?_, by simp, ?_⟩
  · rw [radius_dysonTraceFPowerSeries_eq_top energy hβ V]
  · intro lam _
    simpa [dysonTraceFPowerSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hasSum_dysonTraceCoeff_analyticDysonPartitionFunction energy hβ V lam

/-- Taylor-series packaging at zero for downstream analytic logarithms. -/
theorem hasFPowerSeriesAt_analyticDysonPartitionFunction
    (energy : Config → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    HasFPowerSeriesAt (analyticDysonPartitionFunction energy β V)
      (dysonTraceFPowerSeries energy β V) 0 :=
  (hasFPowerSeriesOnBall_analyticDysonPartitionFunction energy hβ V).hasFPowerSeriesAt

/-- At zero coupling, the analytic partition function is the canonical finite pure-point
partition function for any inverse temperature. -/
@[simp]
theorem analyticDysonPartitionFunction_zero
    (energy : Config → ℝ) (β : ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    analyticDysonPartitionFunction energy β V 0 =
      (QuantumTheory.purePointPartitionFunction energy β : ℂ) := by
  unfold analyticDysonPartitionFunction continuousInteractingHamiltonian
  simp only [zero_smul, add_zero]
  rw [← continuousDiagonalEvolution_eq_exp energy (-β)]
  rw [continuousDiagonalEvolution, finiteOperatorTrace_finiteContinuousOperator,
    traceFock_diagonalEvolution_eq_weightSum]
  simpa only [weightSum] using
    (coe_purePointPartitionFunction_eq_sum_boltzmannWeight energy β).symm

end
end Common
end SecondQuantization

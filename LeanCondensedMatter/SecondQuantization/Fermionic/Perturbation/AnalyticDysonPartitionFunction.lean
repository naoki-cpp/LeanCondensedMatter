import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonTrace
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries

set_option linter.style.header false

/-!
# The analytic finite-dimensional fermionic partition function

For finitely many fermionic modes, the interacting Gibbs operator is a Banach-algebra exponential.
Its Taylor coefficients are the canonical `Common.dysonTraceCoeff` values specialized by the
fermionic energy function.
-/

namespace SecondQuantization
namespace Fermionic

open Filter Set
open scoped Topology

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The genuine finite-dimensional interacting partition function `Tr exp(-β (H₀ + λV))`. -/
noncomputable def analyticDysonPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) : ℂ :=
  Common.finiteOperatorTrace
    (NormedSpace.exp ((-β) • Common.continuousInteractingHamiltonian (fermionEnergy ε) V lam))

omit [LinearOrder Mode] in
/-- The analytic partition function is the thermal trace of the interaction-picture Dyson
operator. -/
theorem analyticDysonPartitionFunction_eq_trace_analyticDysonEvolution
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) :
    analyticDysonPartitionFunction ε β V lam =
      Common.finiteOperatorTrace
        ((Common.continuousDiagonalEvolution (fermionEnergy ε) (-β)).comp
          (Common.analyticDysonEvolution (fermionEnergy ε) V β lam)) := by
  unfold analyticDysonPartitionFunction
  apply congrArg Common.finiteOperatorTrace
  change NormedSpace.exp ((-β) • Common.continuousInteractingHamiltonian (fermionEnergy ε) V lam) =
    Common.continuousDiagonalEvolution (fermionEnergy ε) (-β) *
      Common.analyticDysonEvolution (fermionEnergy ε) V β lam
  exact (Common.continuousDiagonalEvolution_neg_mul_analyticDysonEvolution_eq_exp
    (fermionEnergy ε) V hβ lam).symm

omit [LinearOrder Mode] in
/-- The specialized Common Dyson trace coefficients sum to the analytic partition function. -/
theorem hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) :
    HasSum
      (fun n : ℕ => lam ^ n * Common.dysonTraceCoeff (fermionEnergy ε) β V n)
      (analyticDysonPartitionFunction ε β V lam) := by
  rw [analyticDysonPartitionFunction_eq_trace_analyticDysonEvolution ε hβ V lam]
  exact Common.hasSum_dysonTraceCoeff_eq_trace_analyticDysonEvolution
    (fermionEnergy ε) hβ V lam

omit [LinearOrder Mode] in
/-- The specialized Common Dyson trace coefficients sum by `tsum` to the analytic partition
function. -/
theorem tsum_dysonTraceCoeff_eq_analyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) :
    (∑' n : ℕ, lam ^ n * Common.dysonTraceCoeff (fermionEnergy ε) β V n) =
      analyticDysonPartitionFunction ε β V lam :=
  (hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction ε hβ V lam).tsum_eq

/-- The one-variable formal multilinear series of specialized Common Dyson trace coefficients. -/
noncomputable def dysonPartitionFPowerSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (Common.dysonTraceCoeff (fermionEnergy ε) β V)

omit [LinearOrder Mode] in
@[simp]
theorem coeff_dysonPartitionFPowerSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    (dysonPartitionFPowerSeries ε β V).coeff n =
      Common.dysonTraceCoeff (fermionEnergy ε) β V n := by
  simp [dysonPartitionFPowerSeries]

omit [LinearOrder Mode] in
/-- The formal `PowerSeries` coefficient and analytic formal-multilinear coefficient agree. -/
theorem coeff_dysonPartitionFPowerSeries_eq_coeff_dysonPartitionSeries
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    (dysonPartitionFPowerSeries ε β V).coeff n =
      PowerSeries.coeff n (dysonPartitionSeries ε β V) := by
  rw [coeff_dysonPartitionFPowerSeries, coeff_dysonPartitionSeries,
    dysonPartitionCoeff_eq_dysonTraceCoeff]

omit [LinearOrder Mode] in
/-- The Dyson partition Taylor series has infinite radius of convergence. -/
theorem radius_dysonPartitionFPowerSeries_eq_top
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    (dysonPartitionFPowerSeries ε β V).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs : Summable (fun n : ℕ =>
      ‖(r : ℂ) ^ n * Common.dysonTraceCoeff (fermionEnergy ε) β V n‖) :=
    (hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction
      ε hβ V (r : ℂ)).summable.norm
  simpa [dysonPartitionFPowerSeries, norm_mul, norm_pow, mul_comm] using hs

omit [LinearOrder Mode] in
/-- The analytic partition function has the Common Dyson trace coefficients as its Taylor series. -/
theorem hasFPowerSeriesOnBall_analyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    HasFPowerSeriesOnBall (analyticDysonPartitionFunction ε β V)
      (dysonPartitionFPowerSeries ε β V) 0 ⊤ := by
  refine ⟨?_, by simp, ?_⟩
  · rw [radius_dysonPartitionFPowerSeries_eq_top ε hβ V]
  · intro lam _
    simpa [dysonPartitionFPowerSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction ε hβ V lam

omit [LinearOrder Mode] in
/-- Taylor-series packaging at zero for downstream analytic logarithms. -/
theorem hasFPowerSeriesAt_analyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    HasFPowerSeriesAt (analyticDysonPartitionFunction ε β V)
      (dysonPartitionFPowerSeries ε β V) 0 :=
  (hasFPowerSeriesOnBall_analyticDysonPartitionFunction ε hβ V).hasFPowerSeriesAt

omit [LinearOrder Mode] in
/-- The interacting finite-dimensional partition function is analytic at zero coupling. -/
theorem analyticAt_analyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    AnalyticAt ℂ (analyticDysonPartitionFunction ε β V) 0 :=
  (hasFPowerSeriesAt_analyticDysonPartitionFunction ε hβ V).analyticAt

omit [LinearOrder Mode] in
/-- At zero coupling, the analytic partition function is the free partition function. -/
@[simp]
theorem analyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    analyticDysonPartitionFunction ε β V 0 = freePartitionFunction ε β := by
  rw [← tsum_dysonTraceCoeff_eq_analyticDysonPartitionFunction ε hβ V 0,
    tsum_eq_single 0]
  · rw [← dysonPartitionCoeff_eq_dysonTraceCoeff, dysonPartitionCoeff_zero]
    simp
  · intro n hn
    simp [hn]

omit [LinearOrder Mode] in
/-- The analytic partition function remains nonzero in a neighborhood of zero coupling. -/
theorem analyticDysonPartitionFunction_ne_zero_eventually
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    ∀ᶠ lam in 𝓝 (0 : ℂ), analyticDysonPartitionFunction ε β V lam ≠ 0 := by
  have hzero : analyticDysonPartitionFunction ε β V 0 ≠ 0 := by
    rw [analyticDysonPartitionFunction_zero ε hβ V]
    exact freePartitionFunction_ne_zero ε β
  have hmem : analyticDysonPartitionFunction ε β V 0 ∈ ({0} : Set ℂ)ᶜ := by
    simpa using hzero
  have hnhds : ({0} : Set ℂ)ᶜ ∈ 𝓝 (analyticDysonPartitionFunction ε β V 0) :=
    isClosed_singleton.isOpen_compl.mem_nhds hmem
  simpa using
    (analyticAt_analyticDysonPartitionFunction_zero ε hβ V).continuousAt.eventually hnhds

end
end Fermionic
end SecondQuantization

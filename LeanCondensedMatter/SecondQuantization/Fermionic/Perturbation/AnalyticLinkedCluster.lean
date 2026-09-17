import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.AnalyticDysonPartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option linter.style.header false

/-!
# Analytic fermionic linked-cluster bridge

This module owns the normalized analytic partition/log data and the public identification of local
logarithmic derivatives with coefficients of the formal Dyson logarithm. Formal-power-series
witnesses and recurrence machinery used only to prove that bridge remain private or local. Concrete
connected-diagram endpoints belong to `Fermionic.Diagrammatics.LinkedCluster`.
-/

open scoped BigOperators Topology

namespace SecondQuantization
namespace Fermionic

open Filter Set PowerSeries

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The interacting partition function normalized by its free value. -/
noncomputable def normalizedAnalyticDysonPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) : ℂ :=
  ((freePartitionFunction ε β)⁻¹ • analyticDysonPartitionFunction ε β V) lam

omit [LinearOrder Mode] in
@[simp]
theorem normalizedAnalyticDysonPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    normalizedAnalyticDysonPartitionFunction ε β V 0 = 1 := by
  change (freePartitionFunction ε β)⁻¹ *
    analyticDysonPartitionFunction ε β V 0 = 1
  rw [analyticDysonPartitionFunction_zero ε hβ V]
  exact inv_mul_cancel₀ (freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
private theorem hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    HasFPowerSeriesAt (normalizedAnalyticDysonPartitionFunction ε β V)
      ((freePartitionFunction ε β)⁻¹ • dysonPartitionFPowerSeries ε β V) 0 := by
  change HasFPowerSeriesAt
    ((freePartitionFunction ε β)⁻¹ • analyticDysonPartitionFunction ε β V)
    ((freePartitionFunction ε β)⁻¹ • dysonPartitionFPowerSeries ε β V) 0
  exact (hasFPowerSeriesAt_analyticDysonPartitionFunction ε hβ V).const_smul

/-- The local analytic logarithm of the normalized partition function.

The principal complex logarithm is analytic at the base value `1`, so this is the branch selected
near zero coupling. -/
noncomputable def analyticNormalizedLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (lam : ℂ) : ℂ :=
  Complex.log (normalizedAnalyticDysonPartitionFunction ε β V lam)

omit [LinearOrder Mode] in
@[simp]
theorem analyticNormalizedLogPartitionFunction_zero
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    analyticNormalizedLogPartitionFunction ε β V 0 = 0 := by
  rw [analyticNormalizedLogPartitionFunction,
    normalizedAnalyticDysonPartitionFunction_zero ε hβ V]
  exact Complex.log_one

omit [LinearOrder Mode] in
private theorem iteratedDeriv_normalizedAnalyticDysonPartitionFunction_eq_powerSeriesMomentCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (normalizedAnalyticDysonPartitionFunction ε β V) 0 =
      Combinatorics.powerSeriesMomentCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) n := by
  have hcoeff :
      (((freePartitionFunction ε β)⁻¹ • dysonPartitionFPowerSeries ε β V).coeff n) =
        PowerSeries.coeff n
          (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) := by
    rw [coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff,
      normalizedDysonPartitionCoeff]
    change (freePartitionFunction ε β)⁻¹ *
        (dysonPartitionFPowerSeries ε β V).coeff n =
      dysonPartitionCoeff ε β V n / freePartitionFunction ε β
    rw [coeff_dysonPartitionFPowerSeries, dysonPartitionCoeff_eq_dysonTraceCoeff]
    simp [div_eq_mul_inv, mul_comm]
  rw [Combinatorics.powerSeriesMomentCoeff, ← hcoeff]
  rcases hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction ε hβ V with ⟨r, hseries⟩
  have hfactor := hseries.factorial_smul (1 : ℂ) n
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [← hfactor]
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [one_pow, one_smul, nsmul_eq_mul]

omit [LinearOrder Mode] in
private theorem iteratedDeriv_normalizedAnalyticDysonPartitionFunction_succ_eq_sum_log
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv (n + 1) (normalizedAnalyticDysonPartitionFunction ε β V) 0 =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) *
          iteratedDeriv (k + 1) (analyticNormalizedLogPartitionFunction ε β V) 0 *
          iteratedDeriv (n - k) (normalizedAnalyticDysonPartitionFunction ε β V) 0 := by
  let F : ℂ → ℂ := normalizedAnalyticDysonPartitionFunction ε β V
  let G : ℂ → ℂ := analyticNormalizedLogPartitionFunction ε β V
  have hFseries := hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction ε hβ V
  have hFanalytic : AnalyticAt ℂ F 0 := by
    simpa [F] using hFseries.analyticAt
  have hlog : HasFPowerSeriesAt Complex.log
      (FormalMultilinearSeries.ofScalars ℂ (fun m => -(-1 : ℂ) ^ m / m))
      (normalizedAnalyticDysonPartitionFunction ε β V 0) := by
    rw [normalizedAnalyticDysonPartitionFunction_zero ε hβ V]
    exact hasFPowerSeriesAt_clog_one
  have hGanalytic : AnalyticAt ℂ G 0 := by
    simpa [G, analyticNormalizedLogPartitionFunction] using
      (hlog.comp hFseries).analyticAt
  have hFdiff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ F z := by
    simpa [F] using hFseries.eventually_differentiableAt
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), F z ∈ Complex.slitPlane := by
    have hmem : Complex.slitPlane ∈ 𝓝 (F 0) := by
      rw [show F 0 = 1 by simp [F, normalizedAnalyticDysonPartitionFunction_zero ε hβ V]]
      exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
    exact hFanalytic.continuousAt.eventually hmem
  have hderiv : (fun z => deriv G z * F z) =ᶠ[𝓝 (0 : ℂ)] deriv F := by
    filter_upwards [hFdiff, hslit] with z hdiff hz
    have hlog := (hdiff.hasDerivAt.clog hz).deriv
    have hG : deriv G z = deriv F z / F z := by
      change deriv (fun t => Complex.log (F t)) z = deriv F z / F z
      exact hlog
    rw [hG]
    exact div_mul_cancel₀ _ (Complex.slitPlane_ne_zero hz)
  have hiter := hderiv.iteratedDeriv_eq n
  change iteratedDeriv n (deriv G * F) 0 = iteratedDeriv n (deriv F) 0 at hiter
  rw [iteratedDeriv_mul hGanalytic.deriv.contDiffAt hFanalytic.contDiffAt] at hiter
  simp_rw [← iteratedDeriv_succ'] at hiter
  simpa [F, G] using hiter.symm

omit [LinearOrder Mode] in
private theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_powerSeriesCumulantCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (analyticNormalizedLogPartitionFunction ε β V) 0 =
      Combinatorics.powerSeriesCumulantCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) n := by
  let Z : PowerSeries ℂ :=
    PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    simpa [Z] using
      PowerSeries.constantCoeff_normalizeByConstantCoeff
        (constantCoeff_dysonPartitionSeries_ne_zero ε β V)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [iteratedDeriv_zero,
            analyticNormalizedLogPartitionFunction_zero ε hβ V,
            Combinatorics.powerSeriesCumulantCoeff,
            PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.constantCoeff_logOf hZ]
          simp
      | succ n =>
          have hA :=
            iteratedDeriv_normalizedAnalyticDysonPartitionFunction_succ_eq_sum_log
              ε hβ V n
          rw [iteratedDeriv_normalizedAnalyticDysonPartitionFunction_eq_powerSeriesMomentCoeff
            ε hβ V (n + 1)] at hA
          simp_rw [iteratedDeriv_normalizedAnalyticDysonPartitionFunction_eq_powerSeriesMomentCoeff
            ε hβ V] at hA
          change Combinatorics.powerSeriesMomentCoeff Z (n + 1) = _ at hA
          have hC := Combinatorics.powerSeriesMomentCoeff_succ_recurrence hZ n
          have hsum := hA.symm.trans hC
          rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
          have hprefix :
              (∑ k ∈ Finset.range n,
                (Nat.choose n k : ℂ) *
                  iteratedDeriv (k + 1)
                    (analyticNormalizedLogPartitionFunction ε β V) 0 *
                  Combinatorics.powerSeriesMomentCoeff Z (n - k)) =
              ∑ k ∈ Finset.range n,
                (Nat.choose n k : ℂ) *
                  Combinatorics.powerSeriesCumulantCoeff Z (k + 1) *
                  Combinatorics.powerSeriesMomentCoeff Z (n - k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hklt : k < n := Finset.mem_range.mp hk
            rw [ih (k + 1) (Nat.succ_lt_succ hklt)]
          rw [hprefix] at hsum
          have hlast := add_left_cancel hsum
          simpa [Z, Combinatorics.powerSeriesMomentCoeff,
            constantCoeff_dysonPartitionSeries ε β V,
            freePartitionFunction_ne_zero ε β] using hlast

omit [LinearOrder Mode] in
/-- Analytic logarithmic derivatives agree with the factorial-normalized coefficients of the formal
Dyson logarithm. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (analyticNormalizedLogPartitionFunction ε β V) 0 =
      (n.factorial : ℂ) *
        PowerSeries.coeff n (dysonFormalLogPartitionFunction ε β V) := by
  rw [iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_powerSeriesCumulantCoeff
    ε hβ V n, Combinatorics.powerSeriesCumulantCoeff,
    dysonFormalLogPartitionFunction]

end
end Fermionic
end SecondQuantization

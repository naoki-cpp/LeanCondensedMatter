import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.AnalyticLinkedClusterTheorem
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option linter.style.header false

/-!
# Recurrences for the analytic fermionic logarithmic partition function

The normalized analytic partition function and its local logarithm satisfy the same
moment-cumulant recurrence as the normalized formal Dyson partition series and its formal
logarithm.
-/

open scoped BigOperators Topology

namespace SecondQuantization
namespace Fermionic

open Filter Set

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- Derivatives of the normalized analytic partition function are the exponential-generating
coefficients of the normalized formal Dyson partition series. -/
theorem iteratedDeriv_normalizedAnalyticDysonPartitionFunction_eq_powerSeriesMomentCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (normalizedAnalyticDysonPartitionFunction ε β V) 0 =
      Combinatorics.powerSeriesMomentCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) n := by
  rw [Combinatorics.powerSeriesMomentCoeff,
    ← coeff_normalizedDysonPartitionFPowerSeries_eq_formal]
  have hcanonical :=
    (analyticAt_normalizedAnalyticDysonPartitionFunction_zero ε hβ V).hasFPowerSeriesAt
  have hseries := hasFPowerSeriesAt_normalizedAnalyticDysonPartitionFunction ε hβ V
  have heq := hcanonical.eq_formalMultilinearSeries hseries
  have hcoeff := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hcoeff
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hmul := (div_eq_iff hfac).mp hcoeff
  simpa [mul_comm] using hmul

omit [LinearOrder Mode] in
/-- Leibniz recurrence obtained from the local identity `(log F)' * F = F'`, where `F` is the
normalized analytic partition function. -/
theorem iteratedDeriv_normalizedAnalyticDysonPartitionFunction_succ_eq_sum_log
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
  have hFanalytic := analyticAt_normalizedAnalyticDysonPartitionFunction_zero ε hβ V
  have hGanalytic := analyticAt_analyticNormalizedLogPartitionFunction_zero ε hβ V
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

end
end Fermionic
end SecondQuantization

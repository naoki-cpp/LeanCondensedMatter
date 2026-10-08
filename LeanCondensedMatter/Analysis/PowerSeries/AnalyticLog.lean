import LeanCondensedMatter.Analysis.PowerSeries.MomentCumulantRecurrence
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option linter.style.header false

/-!
# Analytic logarithms and formal power-series logarithms

This file connects a complex analytic function with a formal power series carrying the same Taylor
coefficients. If the common constant term is one, derivatives of the principal analytic logarithm at
the expansion point agree with the factorial-normalized coefficients of the formal logarithm.

The result is independent of any physical realization and supplies the analytic/formal bridge used
by linked-cluster constructions.
-/

open scoped BigOperators Topology

namespace PowerSeries

open Filter Set

noncomputable section

/-- If an analytic function and a formal power series have the same Taylor coefficients at zero and
both are normalized to value/constant coefficient one, then derivatives of the principal analytic
logarithm equal the factorial-normalized coefficients of the formal logarithm. -/
theorem iteratedDeriv_clog_eq_factorial_mul_coeff_logOf
    {F : ℂ → ℂ} {P : FormalMultilinearSeries ℂ ℂ ℂ} {Z : PowerSeries ℂ}
    (hseries : HasFPowerSeriesAt F P 0)
    (hF0 : F 0 = 1)
    (hcoeff : ∀ n : ℕ, P.coeff n = PowerSeries.coeff n Z)
    (hZ : PowerSeries.constantCoeff Z = 1)
    (n : ℕ) :
    iteratedDeriv n (fun z => Complex.log (F z)) 0 =
      (n.factorial : ℂ) * PowerSeries.coeff n (PowerSeries.logOf Z) := by
  have hFanalytic : AnalyticAt ℂ F 0 := hseries.analyticAt
  obtain ⟨r, hseriesBall⟩ := hseries
  have hmoment (m : ℕ) :
      iteratedDeriv m F 0 = Combinatorics.powerSeriesMomentCoeff Z m := by
    rw [Combinatorics.powerSeriesMomentCoeff, ← hcoeff m]
    have hfactor := hseriesBall.factorial_smul (1 : ℂ) m
    rw [iteratedDeriv_eq_iteratedFDeriv, ← hfactor]
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    simp only [one_pow, one_smul, nsmul_eq_mul]
  let G : ℂ → ℂ := fun z => Complex.log (F z)
  have hlog : HasFPowerSeriesAt Complex.log
      (FormalMultilinearSeries.ofScalars ℂ (fun m => -(-1 : ℂ) ^ m / m)) (F 0) := by
    rw [hF0]
    exact hasFPowerSeriesAt_clog_one
  have hGanalytic : AnalyticAt ℂ G 0 := by
    change AnalyticAt ℂ (fun x => Complex.log (F x)) 0
    simpa only [Function.comp_def] using (hlog.comp hseriesBall.hasFPowerSeriesAt).analyticAt
  have hFdiff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ F z := by
    simpa using hseriesBall.hasFPowerSeriesAt.eventually_differentiableAt
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), F z ∈ Complex.slitPlane := by
    have hmem : Complex.slitPlane ∈ 𝓝 (F 0) := by
      rw [hF0]
      exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
    exact hFanalytic.continuousAt.eventually hmem
  have hrecurrence (m : ℕ) :
      iteratedDeriv (m + 1) F 0 =
        ∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℂ) *
            iteratedDeriv (k + 1) G 0 *
            iteratedDeriv (m - k) F 0 := by
    have hderiv : (fun z => deriv G z * F z) =ᶠ[𝓝 (0 : ℂ)] deriv F := by
      filter_upwards [hFdiff, hslit] with z hdiff hz
      have hclog := (hdiff.hasDerivAt.clog hz).deriv
      have hG : deriv G z = deriv F z / F z := by
        change deriv (fun t => Complex.log (F t)) z = deriv F z / F z
        exact hclog
      rw [hG]
      exact div_mul_cancel₀ _ (Complex.slitPlane_ne_zero hz)
    have hiter := hderiv.iteratedDeriv_eq m
    change iteratedDeriv m (deriv G * F) 0 = iteratedDeriv m (deriv F) 0 at hiter
    rw [iteratedDeriv_mul hGanalytic.deriv.contDiffAt hFanalytic.contDiffAt] at hiter
    simp_rw [← iteratedDeriv_succ'] at hiter
    exact hiter.symm
  have hcumulant (m : ℕ) :
      iteratedDeriv m G 0 = Combinatorics.powerSeriesCumulantCoeff Z m := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
        cases m with
        | zero =>
            rw [iteratedDeriv_zero]
            change Complex.log (F 0) =
              Combinatorics.powerSeriesCumulantCoeff Z 0
            rw [hF0, Complex.log_one, Combinatorics.powerSeriesCumulantCoeff,
              PowerSeries.coeff_zero_eq_constantCoeff,
              PowerSeries.constantCoeff_logOf hZ]
            simp
        | succ m =>
            have hA := hrecurrence m
            rw [hmoment (m + 1)] at hA
            simp_rw [hmoment] at hA
            change Combinatorics.powerSeriesMomentCoeff Z (m + 1) = _ at hA
            have hC := Combinatorics.powerSeriesMomentCoeff_succ_recurrence hZ m
            have hsum := hA.symm.trans hC
            rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
            have hprefix :
                (∑ k ∈ Finset.range m,
                  (Nat.choose m k : ℂ) *
                    iteratedDeriv (k + 1) G 0 *
                    Combinatorics.powerSeriesMomentCoeff Z (m - k)) =
                ∑ k ∈ Finset.range m,
                  (Nat.choose m k : ℂ) *
                    Combinatorics.powerSeriesCumulantCoeff Z (k + 1) *
                    Combinatorics.powerSeriesMomentCoeff Z (m - k) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hklt : k < m := Finset.mem_range.mp hk
              rw [ih (k + 1) (Nat.succ_lt_succ hklt)]
            rw [hprefix] at hsum
            have hlast := add_left_cancel hsum
            simpa [Combinatorics.powerSeriesMomentCoeff, hZ] using hlast
  simpa [G, Combinatorics.powerSeriesCumulantCoeff] using hcumulant n

end

end PowerSeries

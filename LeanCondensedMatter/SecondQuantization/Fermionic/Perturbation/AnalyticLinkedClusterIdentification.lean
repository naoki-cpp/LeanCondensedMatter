import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.AnalyticLinkedClusterRecurrence

set_option linter.style.header false

/-!
# Identification of analytic logarithmic derivatives with connected diagrams

The analytic and formal logarithms satisfy the same triangular moment-cumulant recurrence and have
the same zeroth coefficient. Strong induction therefore identifies their coefficients. Composing
this bridge with the formal Dyson linked-cluster theorem gives the analytic connected-diagram
formula.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

open PowerSeries

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The analytic logarithmic derivatives equal the exponential-generating coefficients of the
formal logarithm of the normalized Dyson partition series. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_powerSeriesCumulantCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (analyticNormalizedLogPartitionFunction ε β V) 0 =
      Combinatorics.powerSeriesCumulantCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) n := by
  let Z : PowerSeries ℂ :=
    PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    simpa [Z] using
      constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries ε β V
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
/-- Taylor-coefficient form of the analytic/formal logarithm bridge. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    iteratedDeriv n (analyticNormalizedLogPartitionFunction ε β V) 0 =
      (n.factorial : ℂ) *
        PowerSeries.coeff n (dysonFormalLogPartitionFunction ε β V) := by
  rw [iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_powerSeriesCumulantCoeff
    ε hβ V n, Combinatorics.powerSeriesCumulantCoeff,
    dysonFormalLogPartitionFunction]

/-- Analytic fermionic Dyson linked-cluster theorem: derivatives of the local normalized log
partition function are sums of connected quartic Wick-diagram amplitudes. -/
theorem iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    iteratedDeriv n
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  rw [iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff
    ε hβ (quarticInteraction g) n]
  exact factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
    ε β g n hn

end
end Fermionic
end SecondQuantization

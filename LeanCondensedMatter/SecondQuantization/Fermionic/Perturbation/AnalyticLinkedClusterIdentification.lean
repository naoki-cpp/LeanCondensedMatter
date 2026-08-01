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

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

private theorem derivative_log_mul_one_add_X_for_analytic_bridge :
    d⁄dX ℂ (PowerSeries.log ℂ) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_mk, pow_succ]

private theorem derivative_logOf_mul_for_analytic_bridge {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX ℂ (PowerSeries.logOf Z) * Z = d⁄dX ℂ Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst (Z - 1))
    derivative_log_mul_one_add_X_for_analytic_bridge
  have hone : (1 : PowerSeries ℂ).subst (Z - 1) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hgeom' :
      (d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z = 1 := by
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub, hone] at hgeom
    simpa using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℂ hsub]
  have hderiv : d⁄dX ℂ (Z - 1) = d⁄dX ℂ Z := by simp
  rw [hderiv]
  calc
    ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * d⁄dX ℂ Z) * Z =
        ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z) * d⁄dX ℂ Z := by
          ring
    _ = d⁄dX ℂ Z := by rw [hgeom']; simp

private theorem powerSeriesMomentCoeff_succ_recurrence_for_analytic_bridge
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z = 1) (n : ℕ) :
    Combinatorics.powerSeriesMomentCoeff Z (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * Combinatorics.powerSeriesCumulantCoeff Z (k + 1) *
          Combinatorics.powerSeriesMomentCoeff Z (n - k) := by
  have hcoeff := congrArg (PowerSeries.coeff n)
    (derivative_logOf_mul_for_analytic_bridge hZ)
  rw [PowerSeries.coeff_mul] at hcoeff
  simp_rw [PowerSeries.coeff_derivative] at hcoeff
  calc
    Combinatorics.powerSeriesMomentCoeff Z (n + 1) =
        (n.factorial : ℂ) * (PowerSeries.coeff (n + 1) Z * (n + 1 : ℂ)) := by
          simp [Combinatorics.powerSeriesMomentCoeff, Nat.factorial_succ]
          ring
    _ = (n.factorial : ℂ) *
        (∑ p ∈ Finset.antidiagonal n,
          PowerSeries.coeff (p.1 + 1) (PowerSeries.logOf Z) * (p.1 + 1 : ℂ) *
            PowerSeries.coeff p.2 Z) := by rw [hcoeff]
    _ = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * Combinatorics.powerSeriesCumulantCoeff Z (k + 1) *
          Combinatorics.powerSeriesMomentCoeff Z (n - k) := by
      rw [Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hnat := Nat.choose_mul_factorial_mul_factorial hkn
      have hfac :
          (n.factorial : ℂ) * (k + 1 : ℂ) =
            (Nat.choose n k : ℂ) * ((k + 1).factorial : ℂ) *
              ((n - k).factorial : ℂ) := by
        norm_cast
        calc
          n.factorial * (k + 1) = (k + 1) * n.factorial := by ac_rfl
          _ = (k + 1) * (Nat.choose n k * k.factorial * (n - k).factorial) := by
            rw [hnat]
          _ = Nat.choose n k * (k + 1).factorial * (n - k).factorial := by
            rw [Nat.factorial_succ]
            ac_rfl
      simp only [Combinatorics.powerSeriesMomentCoeff,
        Combinatorics.powerSeriesCumulantCoeff]
      calc
        (n.factorial : ℂ) *
            (PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) * (k + 1 : ℂ) *
              PowerSeries.coeff (n - k) Z) =
            ((n.factorial : ℂ) * (k + 1 : ℂ)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by ring
        _ = ((Nat.choose n k : ℂ) * ((k + 1).factorial : ℂ) *
              ((n - k).factorial : ℂ)) *
              PowerSeries.coeff (k + 1) (PowerSeries.logOf Z) *
                PowerSeries.coeff (n - k) Z := by rw [hfac]
        _ = (Nat.choose n k : ℂ) *
              (((k + 1).factorial : ℂ) *
                PowerSeries.coeff (k + 1) (PowerSeries.logOf Z)) *
              (((n - k).factorial : ℂ) * PowerSeries.coeff (n - k) Z) := by ring

omit [LinearOrder Mode] in
/-- The analytic logarithmic derivatives equal the exponential-generating coefficients of the
formal logarithm of the normalized Dyson partition series. -/
theorem iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_powerSeriesCumulantCoeff
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (n : ℕ) :
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
          have hC := powerSeriesMomentCoeff_succ_recurrence_for_analytic_bridge hZ n
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
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (n : ℕ) :
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

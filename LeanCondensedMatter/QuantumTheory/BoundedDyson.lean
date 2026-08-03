import LeanCondensedMatter.Analysis.Dyson.Constant
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.header false

/-!
# Bounded-operator Dyson evolution

This module specializes the dimension-independent `Analysis.Dyson` API to bounded operators on an
arbitrary complete complex Hilbert space. The generic `Dyson` namespace remains the owner of the
coefficients, convergence proofs, Volterra equation, uniqueness theorem, and constant-generator
exponential bridge. The results below discharge the algebra-unit norm hypothesis for continuous
linear endomorphisms and provide a `QuantumTheory`-level entry point for time-dependent bounded
perturbations.

No finite-dimensional hypothesis is used. Unbounded Hamiltonians and perturbations are deliberately
outside this API: their propagators require domain invariance, closedness, and other operator-domain
arguments not represented by `H →L[ℂ] H`.
-/

namespace QuantumTheory
namespace BoundedDyson

open Set

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The identity bounded operator has norm at most one, including on the trivial Hilbert space. -/
theorem norm_one_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
  change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
  exact ContinuousLinearMap.norm_id_le

/-- Factorial norm control for bounded-operator Dyson coefficients. -/
theorem norm_coeff_le_of_bound (V : ℝ → (H →L[ℂ] H)) {β M : ℝ}
    (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖Dyson.coeff V n τ‖ ≤ Dyson.majorant M τ n := by
  exact Dyson.norm_coeff_le_of_bound V norm_one_le hM hV n hτ

/-- Factorial norm control for perturbatively weighted bounded-operator Dyson terms. -/
theorem norm_term_le_of_bound (V : ℝ → (H →L[ℂ] H)) {β M : ℝ}
    (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖Dyson.term V lam τ n‖ ≤ Dyson.majorant (‖lam‖ * M) τ n := by
  exact Dyson.norm_term_le_of_bound V norm_one_le hM hV lam n hτ

/-- The bounded-operator Dyson series has the generic evolution as its sum. -/
theorem hasSum_evolution_of_bound (V : ℝ → (H →L[ℂ] H)) {β M : ℝ}
    (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    HasSum (Dyson.term V lam τ) (Dyson.evolution V lam τ) := by
  exact Dyson.hasSum_evolution_of_bound V norm_one_le hM hV lam hτ

/-- A continuous uniformly bounded operator interaction has continuous Dyson evolution. -/
theorem continuousOn_evolution_of_bound {V : ℝ → (H →L[ℂ] H)} (hVcont : Continuous V)
    {β M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M) (lam : ℂ) :
    ContinuousOn (fun τ => Dyson.evolution V lam τ) (Icc (0 : ℝ) β) := by
  exact Dyson.continuousOn_evolution_of_bound hVcont norm_one_le hM hV lam

/-- The bounded-operator Dyson evolution satisfies the interaction-picture Volterra equation. -/
theorem evolution_eq_one_sub_integral_of_bound
    {V : ℝ → (H →L[ℂ] H)} (hVcont : Continuous V)
    {β M τ : ℝ} (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    Dyson.evolution V lam τ =
      1 - lam • ∫ σ in (0 : ℝ)..τ, V σ * Dyson.evolution V lam σ := by
  exact Dyson.evolution_eq_one_sub_integral_of_bound hVcont norm_one_le hM hV hτ lam

/-- The generic Dyson series is the unique continuous bounded-operator solution of its Volterra
equation on a compact nonnegative time interval. -/
theorem eqOn_evolution_of_volterra_of_bound
    {V U : ℝ → (H →L[ℂ] H)} (hVcont : Continuous V)
    {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M) (lam : ℂ)
    (hU : ContinuousOn U (Icc (0 : ℝ) β))
    (hUEq : ∀ t ∈ Icc (0 : ℝ) β,
      U t = 1 - lam • ∫ σ in (0 : ℝ)..t, V σ * U σ) :
    EqOn U (fun t => Dyson.evolution V lam t) (Icc (0 : ℝ) β) := by
  exact Dyson.eqOn_evolution_of_volterra_of_bound
    hVcont hβ norm_one_le hM hV lam hU hUEq

/-- For a constant bounded operator, the Dyson evolution is the Banach-algebra exponential. -/
theorem evolution_const_eq_exp_of_nonneg (K : H →L[ℂ] H) (lam : ℂ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    Dyson.evolution (fun _ : ℝ => K) lam τ =
      NormedSpace.exp (-(((τ : ℝ) • lam) • K)) := by
  exact Dyson.evolution_const_eq_exp_of_nonneg K lam hτ norm_one_le

end
end BoundedDyson
end QuantumTheory

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Dimension-independent bounded Dyson coefficients

This module owns the state-independent analytic core of the bounded Dyson expansion.  It is
parameterized only by a complete complex normed algebra and therefore does not depend on a finite
basis, Fock space, Gibbs state, or KMS structure.

The recursive coefficients use the sign convention

`D₀(τ) = 1`, `Dₙ₊₁(τ) = -∫₀ᵗ V(σ) Dₙ(σ) dσ`.

Continuity, factorial bounds, convergence, and the Volterra equation are added in later modules;
this file fixes the generic owner and the scalar majorant used by those proofs.
-/

namespace Dyson

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The recursively defined bounded Dyson coefficient in a complete complex normed algebra. -/
noncomputable def coeff (V : ℝ → A) : ℕ → ℝ → A
  | 0, _ => 1
  | n + 1, τ => - ∫ σ in (0 : ℝ)..τ, V σ * coeff V n σ

omit [CompleteSpace A] in
@[simp]
theorem coeff_zero (V : ℝ → A) (τ : ℝ) : coeff V 0 τ = 1 := rfl

omit [CompleteSpace A] in
/-- The defining successor recursion for generic Dyson coefficients. -/
theorem coeff_succ (V : ℝ → A) (n : ℕ) (τ : ℝ) :
    coeff V (n + 1) τ = - ∫ σ in (0 : ℝ)..τ, V σ * coeff V n σ := rfl

omit [CompleteSpace A] in
/-- At the initial time, only the zeroth Dyson coefficient survives. -/
@[simp]
theorem coeff_at_zero (V : ℝ → A) (n : ℕ) :
    coeff V n 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ]

/-- The `n`th perturbatively weighted Dyson coefficient. -/
noncomputable def term (V : ℝ → A) (lam : ℂ) (τ : ℝ) (n : ℕ) : A :=
  lam ^ n • coeff V n τ

omit [CompleteSpace A] in
@[simp]
theorem term_zero (V : ℝ → A) (lam : ℂ) (τ : ℝ) : term V lam τ 0 = 1 := by
  simp [term]

omit [CompleteSpace A] in
/-- At the initial time, all positive-order weighted coefficients vanish. -/
@[simp]
theorem term_at_zero (V : ℝ → A) (lam : ℂ) (n : ℕ) :
    term V lam 0 n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [term]
  · simp [term, coeff_at_zero, hn]

/-- The formal norm-topological Dyson evolution, defined as the `tsum` of weighted coefficients. -/
noncomputable def evolution (V : ℝ → A) (lam : ℂ) (τ : ℝ) : A :=
  ∑' n : ℕ, term V lam τ n

omit [CompleteSpace A] in
/-- The generic Dyson evolution starts at the algebra unit. -/
@[simp]
theorem evolution_zero (V : ℝ → A) (lam : ℂ) : evolution V lam 0 = 1 := by
  rw [evolution, tsum_eq_single 0]
  · simp [term]
  · intro n hn
    simp [term, coeff_at_zero, hn]

/-- The scalar exponential-series majorant `(M τ)ⁿ / n!`. -/
noncomputable def majorant (M τ : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ)⁻¹ * (M * τ) ^ n

@[simp]
theorem majorant_zero (M τ : ℝ) : majorant M τ 0 = 1 := by
  simp [majorant]

/-- The Dyson majorant is nonnegative for nonnegative `M` and `τ`. -/
theorem majorant_nonneg {M τ : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ) (n : ℕ) :
    0 ≤ majorant M τ n := by
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (pow_nonneg (mul_nonneg hM hτ) n)

/-- Integrating one more bounded interaction factor advances the factorial majorant by one order. -/
theorem integral_mul_majorant (M τ : ℝ) (n : ℕ) :
    ∫ σ in (0 : ℝ)..τ, M * majorant M σ n = majorant M τ (n + 1) := by
  have hfun : (fun σ : ℝ => M * majorant M σ n) =
      fun σ : ℝ => ((n.factorial : ℝ)⁻¹ * M ^ (n + 1)) * σ ^ n := by
    funext σ
    simp only [majorant, mul_pow]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, majorant,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
  field_simp [Nat.factorial_ne_zero]

/-- The scalar factorial majorant is summable for every real `M` and `τ`. -/
theorem summable_majorant (M τ : ℝ) : Summable (majorant M τ) := by
  refine (Real.summable_pow_div_factorial (M * τ)).congr ?_
  intro n
  simp [majorant, div_eq_mul_inv, mul_comm]

/-- The factorial majorant is monotone in nonnegative time. -/
theorem majorant_mono_time {M τ β : ℝ} (hM : 0 ≤ M)
    (hτ : 0 ≤ τ) (hτβ : τ ≤ β) (n : ℕ) :
    majorant M τ n ≤ majorant M β n := by
  unfold majorant
  gcongr

end
end Dyson

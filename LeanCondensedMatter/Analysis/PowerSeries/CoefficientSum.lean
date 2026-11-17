import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Coefficientwise complex sums of formal power series

A general formal series in ℂ⟦X⟧ need not converge at a complex number.
The additive and Cauchy-product laws below therefore require explicit summability
hypotheses. Constant multiplication and multiplication by X also hold for the total
infinite sum without summability. Crucially, the Cauchy-product theorem below
transports formal multiplication to *actual complex series* without claiming
that Mathlib's topologically nilpotent `PowerSeries.eval₂` can be used
at an arbitrary complex value.
-/

namespace PowerSeries

noncomputable section

open scoped BigOperators PowerSeries

/-- The total coefficientwise complex infinite sum. This does not assert convergence;
addition, subtraction, and Cauchy multiplication retain explicit summability hypotheses. -/
noncomputable def coefficientSum (f : ℂ⟦X⟧) (x : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n f * x ^ n

private theorem coeff_mul_mul_pow (f g : ℂ⟦X⟧) (x : ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * x ^ n =
      ∑ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff p.1 f * x ^ p.1) *
          (PowerSeries.coeff p.2 g * x ^ p.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

/-- An absolutely convergent pair of coefficientwise series admits
Cauchy multiplication, with the product coefficients coming from the
*formal* power-series multiplication in ℂ⟦X⟧. -/
theorem coefficientSum_mul (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    coefficientSum (f * g) x =
      coefficientSum f x * coefficientSum g x := by
  simpa only [coefficientSum, ← coeff_mul_mul_pow f g x] using
    (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.norm hg.norm).symm

/-- Addition commutes with coefficientwise evaluation when both terms are summable. -/
theorem coefficientSum_add (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    coefficientSum (f + g) x =
      coefficientSum f x + coefficientSum g x := by
  simpa only [coefficientSum, map_add, add_mul] using hf.tsum_add hg

/-- Subtraction commutes with coefficientwise evaluation when both terms are summable. -/
theorem coefficientSum_sub (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    coefficientSum (f - g) x =
      coefficientSum f x - coefficientSum g x := by
  simpa only [coefficientSum, map_sub, sub_mul] using hf.tsum_sub hg

/-- Cauchy convolution is itself summable when the two coefficientwise
series are absolutely summable. This makes multiplication composable with
addition and multiplication by X. -/
theorem summable_coefficientSum_mul (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    Summable (fun n : ℕ => PowerSeries.coeff n (f * g) * x ^ n) := by
  simpa only [← coeff_mul_mul_pow f g x] using
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hf.norm hg.norm).of_norm

/-- Addition preserves summable coefficientwise complex evaluation. -/
theorem summable_coefficientSum_add (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    Summable (fun n : ℕ => PowerSeries.coeff n (f + g) * x ^ n) := by
  simpa only [map_add, add_mul] using hf.add hg

/-- Multiplication by a complex constant preserves coefficientwise summability. -/
theorem summable_coefficientSum_C_mul (f : ℂ⟦X⟧) (x c : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    Summable (fun n : ℕ => PowerSeries.coeff n (PowerSeries.C c * f) * x ^ n) := by
  simpa only [PowerSeries.coeff_C_mul, mul_assoc] using hf.mul_left c

/-- Multiplication by a complex constant commutes with the total coefficientwise sum,
including when the coefficient sequence is not summable. -/
theorem coefficientSum_C_mul (f : ℂ⟦X⟧) (x c : ℂ) :
    coefficientSum (PowerSeries.C c * f) x = c * coefficientSum f x := by
  simp only [coefficientSum, PowerSeries.coeff_C_mul, mul_assoc, tsum_mul_left]

/-- Formal multiplication by X shifts a summable coefficient sequence
and therefore preserves convergence at the chosen complex argument. -/
theorem summable_coefficientSum_X_mul (f : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.X * f) * x ^ n) := by
  apply (summable_nat_add_iff 1).1
  simpa only [Nat.add_one, PowerSeries.coeff_succ_X_mul, pow_succ,
    mul_comm, mul_left_comm, mul_assoc] using hf.mul_left x

/-- Multiplication by X commutes with the total coefficientwise sum: its zero constant
coefficient permits an unconditional shift of the series. -/
theorem coefficientSum_X_mul (f : ℂ⟦X⟧) (x : ℂ) :
    coefficientSum (PowerSeries.X * f) x = x * coefficientSum f x := by
  have hshift :
      (∑' n : ℕ, PowerSeries.coeff (n + 1) (PowerSeries.X * f) * x ^ (n + 1)) =
        ∑' n : ℕ, PowerSeries.coeff n (PowerSeries.X * f) * x ^ n := by
    apply Nat.succ_injective.tsum_eq
      (f := fun n : ℕ => PowerSeries.coeff n (PowerSeries.X * f) * x ^ n)
    intro n hn
    cases n with
    | zero => exact (hn (by simp only [PowerSeries.coeff_zero_X_mul, zero_mul])).elim
    | succ n => exact ⟨n, rfl⟩
  unfold coefficientSum
  rw [← hshift]
  calc
    (∑' n : ℕ,
      PowerSeries.coeff (n + 1) (PowerSeries.X * f) * x ^ (n + 1)) =
        ∑' n : ℕ, x * (PowerSeries.coeff n f * x ^ n) := by
      apply tsum_congr
      intro n
      rw [PowerSeries.coeff_succ_X_mul, pow_succ]
      ring
    _ = x * (∑' n : ℕ, PowerSeries.coeff n f * x ^ n) := tsum_mul_left

/-- The unit formal power series evaluates to one. -/
theorem coefficientSum_one (x : ℂ) :
    coefficientSum (1 : ℂ⟦X⟧) x = 1 := by
  simp [coefficientSum, PowerSeries.coeff_one]

end

end PowerSeries

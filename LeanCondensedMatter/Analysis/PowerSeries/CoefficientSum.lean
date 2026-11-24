import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Coefficientwise sums of formal power series

A general formal series in R⟦X⟧ need not converge at a field element.
The additive and Cauchy-product laws below therefore require explicit summability
hypotheses. Constant multiplication and multiplication by X also hold for the total
infinite sum without summability. Crucially, the Cauchy-product theorem below
transports formal multiplication to *convergent series* without claiming
that Mathlib's topologically nilpotent `PowerSeries.eval₂` can be used
at an arbitrary field element.
-/

namespace PowerSeries

noncomputable section

open scoped BigOperators PowerSeries

variable {R : Type*} [NormedField R]

/-- The total coefficientwise infinite sum. This does not assert convergence;
addition, subtraction, and Cauchy multiplication retain explicit summability hypotheses. -/
noncomputable def coefficientSum (f : R⟦X⟧) (x : R) : R :=
  ∑' n : ℕ, PowerSeries.coeff n f * x ^ n

private theorem coeff_mul_mul_pow (f g : R⟦X⟧) (x : R) (n : ℕ) :
    PowerSeries.coeff n (f * g) * x ^ n =
      ∑ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff p.1 f * x ^ p.1) *
          (PowerSeries.coeff p.2 g * x ^ p.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

/-- Absolutely convergent formal coefficient series multiply by the Cauchy-product law.
The sum witness includes both the value and convergence. -/
theorem hasSum_coefficientSum_mul [CompleteSpace R] (f g : R⟦X⟧) (x : R)
    {a b : R}
    (hf : HasSum (fun n : ℕ => PowerSeries.coeff n f * x ^ n) a)
    (hg : HasSum (fun n : ℕ => PowerSeries.coeff n g * x ^ n) b)
    (hfn : Summable (fun n : ℕ => ‖PowerSeries.coeff n f * x ^ n‖))
    (hgn : Summable (fun n : ℕ => ‖PowerSeries.coeff n g * x ^ n‖)) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (f * g) * x ^ n) (a * b) := by
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  rw [← hf.tsum_eq, ← hg.tsum_eq,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn]
  simpa only [← coeff_mul_mul_pow f g x] using hs.hasSum

/-- Addition of convergent formal coefficient series. -/
theorem hasSum_coefficientSum_add (f g : R⟦X⟧) (x : R) {a b : R}
    (hf : HasSum (fun n : ℕ => PowerSeries.coeff n f * x ^ n) a)
    (hg : HasSum (fun n : ℕ => PowerSeries.coeff n g * x ^ n) b) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (f + g) * x ^ n) (a + b) := by
  simpa only [map_add, add_mul] using hf.add hg

/-- Subtraction of convergent formal coefficient series. -/
theorem hasSum_coefficientSum_sub (f g : R⟦X⟧) (x : R) {a b : R}
    (hf : HasSum (fun n : ℕ => PowerSeries.coeff n f * x ^ n) a)
    (hg : HasSum (fun n : ℕ => PowerSeries.coeff n g * x ^ n) b) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (f - g) * x ^ n) (a - b) := by
  simpa only [map_sub, sub_mul] using hf.sub hg

/-- Multiplication by a constant scales the sum witness. -/
theorem hasSum_coefficientSum_C_mul (f : R⟦X⟧) (x c : R) {a : R}
    (hf : HasSum (fun n : ℕ => PowerSeries.coeff n f * x ^ n) a) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.C c * f) * x ^ n) (c * a) := by
  simpa only [PowerSeries.coeff_C_mul, mul_assoc] using hf.mul_left c

/-- Multiplication by a field constant commutes with the total coefficientwise sum,
including when the coefficient sequence is not summable. -/
theorem coefficientSum_C_mul (f : R⟦X⟧) (x c : R) :
    coefficientSum (PowerSeries.C c * f) x = c * coefficientSum f x := by
  simp only [coefficientSum, PowerSeries.coeff_C_mul, mul_assoc, tsum_mul_left]

/-- Formal multiplication by X shifts the coefficient sequence and scales its sum. -/
theorem hasSum_coefficientSum_X_mul (f : R⟦X⟧) (x : R) {a : R}
    (hf : HasSum (fun n : ℕ => PowerSeries.coeff n f * x ^ n) a) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.X * f) * x ^ n) (x * a) := by
  have hshift : HasSum (fun n : ℕ =>
      PowerSeries.coeff (n + 1) (PowerSeries.X * f) * x ^ (n + 1)) (x * a) := by
    simp only [Nat.add_one, PowerSeries.coeff_succ_X_mul, pow_succ]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hf.mul_left x
  simpa only [Finset.sum_range_one, PowerSeries.coeff_zero_X_mul, zero_mul, add_zero] using
    (hasSum_nat_add_iff 1).mp hshift

/-- Multiplication by X commutes with the total coefficientwise sum: its zero constant
coefficient permits an unconditional shift of the series. -/
theorem coefficientSum_X_mul (f : R⟦X⟧) (x : R) :
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
  simp_rw [PowerSeries.coeff_succ_X_mul, pow_succ, ← mul_assoc]
  rw [tsum_mul_right, mul_comm]

/-- The unit formal power series evaluates to one. -/
theorem coefficientSum_one (x : R) :
    coefficientSum (1 : R⟦X⟧) x = 1 := by
  simp [coefficientSum, PowerSeries.coeff_one]

end

end PowerSeries

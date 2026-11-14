import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Absolutely convergent evaluation of formal power-series coefficients

A general formal series in ℂ⟦X⟧ need not converge at a complex number.
The coefficientwise evaluation below is therefore used only with explicit
summability hypotheses. Crucially, the Cauchy-product theorem below
transports formal multiplication to *actual complex series* without claiming
that Mathlib's topologically nilpotent `PowerSeries.eval₂` can be used
at an arbitrary complex value.
-/

namespace PowerSeries

noncomputable section

open scoped BigOperators PowerSeries

/-- The coefficientwise infinite sum. This is only used with an explicit
`Summable` witness for algebraic laws; the total infinite sum alone does not assert convergence. -/
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
  unfold coefficientSum
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.norm hg.norm]
  apply tsum_congr
  intro n
  exact coeff_mul_mul_pow f g x n

/-- Addition commutes with coefficientwise evaluation when both terms are summable. -/
theorem coefficientSum_add (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    coefficientSum (f + g) x =
      coefficientSum f x + coefficientSum g x := by
  unfold coefficientSum
  calc
    (∑' n : ℕ, PowerSeries.coeff n (f + g) * x ^ n) =
        ∑' n : ℕ,
          (PowerSeries.coeff n f * x ^ n + PowerSeries.coeff n g * x ^ n) := by
      apply tsum_congr
      intro n
      rw [map_add]
      ring
    _ = _ := hf.tsum_add hg

/-- Subtraction commutes with coefficientwise evaluation when both terms are summable. -/
theorem coefficientSum_sub (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    coefficientSum (f - g) x =
      coefficientSum f x - coefficientSum g x := by
  unfold coefficientSum
  calc
    (∑' n : ℕ, PowerSeries.coeff n (f - g) * x ^ n) =
        ∑' n : ℕ,
          (PowerSeries.coeff n f * x ^ n - PowerSeries.coeff n g * x ^ n) := by
      apply tsum_congr
      intro n
      rw [map_sub]
      ring
    _ = _ := hf.tsum_sub hg

/-- Cauchy convolution is itself summable when the two coefficientwise
series are absolutely summable. This makes multiplication composable with
addition and multiplication by X. -/
theorem summable_coefficientSum_mul (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    Summable (fun n : ℕ => PowerSeries.coeff n (f * g) * x ^ n) := by
  have hs :
      Summable (fun n : ℕ =>
        ∑ p ∈ Finset.antidiagonal n,
          (PowerSeries.coeff p.1 f * x ^ p.1) *
            (PowerSeries.coeff p.2 g * x ^ p.2)) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hf.norm hg.norm).of_norm
  convert hs using 1
  funext n
  exact coeff_mul_mul_pow f g x n

/-- Addition preserves summable coefficientwise complex evaluation. -/
theorem summable_coefficientSum_add (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    Summable (fun n : ℕ => PowerSeries.coeff n (f + g) * x ^ n) := by
  convert hf.add hg using 1
  funext n
  rw [map_add]
  ring

/-- Scaling a formal series by two preserves convergence. -/
theorem summable_coefficientSum_two_mul (f : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    Summable (fun n : ℕ => PowerSeries.coeff n (2 * f) * x ^ n) := by
  convert hf.mul_left (2 : ℂ) using 1
  funext n
  rw [PowerSeries.coeff_ofNat_mul]
  ring

/-- Scaling a formal series by two commutes with convergent evaluation. -/
theorem coefficientSum_two_mul (f : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    coefficientSum (2 * f) x =
      2 * coefficientSum f x := by
  unfold coefficientSum
  calc
    (∑' n : ℕ, PowerSeries.coeff n (2 * f) * x ^ n) =
        ∑' n : ℕ, (2 : ℂ) * (PowerSeries.coeff n f * x ^ n) := by
      apply tsum_congr
      intro n
      rw [PowerSeries.coeff_ofNat_mul]
      ring
    _ = (2 : ℂ) * (∑' n : ℕ, PowerSeries.coeff n f * x ^ n) :=
      hf.tsum_mul_left 2

/-- Formal multiplication by X shifts a summable coefficient sequence
and therefore preserves convergence at the chosen complex argument. -/
theorem summable_coefficientSum_X_mul (f : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.X * f) * x ^ n) := by
  have htail :
      Summable (fun n : ℕ =>
        PowerSeries.coeff (n + 1) (PowerSeries.X * f) * x ^ (n + 1)) := by
    convert hf.mul_left x using 1
    funext n
    rw [PowerSeries.coeff_succ_X_mul, pow_succ]
    ring
  apply (summable_nat_add_iff 1).1
  simpa only [Nat.add_one] using htail

/-- The formal product by X is compatible with coefficientwise evaluation
at any complex argument whenever the original series is summable. -/
theorem coefficientSum_X_mul (f : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    coefficientSum (PowerSeries.X * f) x =
      x * coefficientSum f x := by
  have hall := summable_coefficientSum_X_mul f x hf
  unfold coefficientSum
  rw [hall.tsum_eq_zero_add]
  simp only [PowerSeries.coeff_zero_X_mul, zero_mul, zero_add]
  calc
    (∑' n : ℕ,
      PowerSeries.coeff (n + 1) (PowerSeries.X * f) * x ^ (n + 1)) =
        ∑' n : ℕ, x * (PowerSeries.coeff n f * x ^ n) := by
      apply tsum_congr
      intro n
      rw [PowerSeries.coeff_succ_X_mul, pow_succ]
      ring
    _ = x * (∑' n : ℕ, PowerSeries.coeff n f * x ^ n) :=
      hf.tsum_mul_left x

/-- The unit formal power series evaluates to one. -/
theorem coefficientSum_one (x : ℂ) :
    coefficientSum (1 : ℂ⟦X⟧) x = 1 := by
  simp [coefficientSum, PowerSeries.coeff_one]

end

end PowerSeries

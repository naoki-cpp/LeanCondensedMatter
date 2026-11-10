import LeanCondensedMatter.Transport.Analysis.BesselJFormalAnalyticBridge
import LeanCondensedMatter.Transport.Analysis.BesselYFormalAnalyticBridge
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

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

namespace QuantumTheory.Transport

noncomputable section

open scoped PowerSeries

/-- The coefficientwise infinite sum. This is only used with an explicit
`Summable` witness; it is not a global power-series evaluation map. -/
noncomputable def besselEntireCoefficientEval (f : ℂ⟦X⟧) (x : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n f * x ^ n

/-- An absolutely convergent pair of coefficientwise series admits
Cauchy multiplication, with the product coefficients coming from the
*formal* power-series multiplication in ℂ⟦X⟧. -/
theorem besselEntireCoefficientEval_mul (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    besselEntireCoefficientEval (f * g) x =
      besselEntireCoefficientEval f x * besselEntireCoefficientEval g x := by
  unfold besselEntireCoefficientEval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.norm hg.norm]
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [← hp', pow_add]
  ring

/-- Transport of addition, requiring both terms to be summable. -/
theorem besselEntireCoefficientEval_add (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    besselEntireCoefficientEval (f + g) x =
      besselEntireCoefficientEval f x + besselEntireCoefficientEval g x := by
  unfold besselEntireCoefficientEval
  calc
    (∑' n : ℕ, PowerSeries.coeff n (f + g) * x ^ n) =
        ∑' n : ℕ,
          (PowerSeries.coeff n f * x ^ n + PowerSeries.coeff n g * x ^ n) := by
      apply tsum_congr
      intro n
      rw [map_add]
      ring
    _ = _ := hf.tsum_add hg

/-- Transport of subtraction, requiring both terms to be summable. -/
theorem besselEntireCoefficientEval_sub (f g : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n))
    (hg : Summable (fun n : ℕ => PowerSeries.coeff n g * x ^ n)) :
    besselEntireCoefficientEval (f - g) x =
      besselEntireCoefficientEval f x - besselEntireCoefficientEval g x := by
  unfold besselEntireCoefficientEval
  calc
    (∑' n : ℕ, PowerSeries.coeff n (f - g) * x ^ n) =
        ∑' n : ℕ,
          (PowerSeries.coeff n f * x ^ n - PowerSeries.coeff n g * x ^ n) := by
      apply tsum_congr
      intro n
      rw [map_sub]
      ring
    _ = _ := hf.tsum_sub hg

/-- The formal product by X is compatible with coefficientwise evaluation
at any complex argument whenever the original series is summable. -/
theorem besselEntireCoefficientEval_X_mul (f : ℂ⟦X⟧) (x : ℂ)
    (hf : Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n)) :
    besselEntireCoefficientEval (PowerSeries.X * f) x =
      x * besselEntireCoefficientEval f x := by
  have htail :
      Summable (fun n : ℕ =>
        PowerSeries.coeff (n + 1) (PowerSeries.X * f) * x ^ (n + 1)) := by
    convert hf.mul_left x using 1
    funext n
    rw [PowerSeries.coeff_succ_X_mul, pow_succ]
    ring
  have hall :
      Summable (fun n : ℕ =>
        PowerSeries.coeff n (PowerSeries.X * f) * x ^ n) := by
    apply (summable_nat_add_iff 1).2
    simpa only [Nat.add_one] using htail
  unfold besselEntireCoefficientEval
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
theorem besselEntireCoefficientEval_one (x : ℂ) :
    besselEntireCoefficientEval (1 : ℂ⟦X⟧) x = 1 := by
  simp [besselEntireCoefficientEval, PowerSeries.coeff_one]

end

end QuantumTheory.Transport

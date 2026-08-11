import LeanCondensedMatter.Combinatorics.PermutationAssignmentCycleTrace
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Exponential normalization of assignment-summed cycle kernels

This file supplies the coefficient-level EGF normalization for W3. The zero-label term is set to
zero explicitly: the connected formal series has no constant term, whereas the raw empty-label
permutation sum is not the matrix-trace coefficient used for positive orders.
-/

namespace Combinatorics

open Finset

variable {ι : Type*} [Fintype ι]

/-- The connected EGF coefficient obtained from assignment-summed single-cycle contributions.

At positive order this is the raw assignment sum divided by `m!`. At order zero it is defined to
be zero, matching the constant term of a connected/logarithmic series. -/
noncomputable def assignmentSingleCycleEGFCoeff
    (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0
  else
    (∑ x : Fin m → ι,
      singleCycleContribution ζ (fun a b : Fin m => K (x a) (x b)) Finset.univ) /
        (Nat.factorial m : ℂ)

@[simp]
theorem assignmentSingleCycleEGFCoeff_zero
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    assignmentSingleCycleEGFCoeff ζ K 0 = 0 := by
  simp [assignmentSingleCycleEGFCoeff]

private theorem factorial_pred_div_factorial_complex (m : ℕ) (hm : 0 < m) :
    (Nat.factorial (m - 1) : ℂ) / (Nat.factorial m : ℂ) = 1 / (m : ℂ) := by
  cases m with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one, Nat.factorial_succ]
      push_cast
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hn, hfac]

/-- EGF normalization changes the `(m - 1)!` multiplicity of full cycles into the universal
`1 / m` cyclic factor. -/
theorem assignmentSingleCycleEGFCoeff_eq_pow_mul_trace_div
    [DecidableEq ι] (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) (hm : 0 < m) :
    assignmentSingleCycleEGFCoeff ζ K m =
      ζ ^ (m - 1) * Matrix.trace (K ^ m) / (m : ℂ) := by
  rw [assignmentSingleCycleEGFCoeff, if_neg (Nat.ne_of_gt hm)]
  rw [sum_singleCycleContribution_assignments_eq_pow_mul_assignmentSingleCycleKernelSum]
  rw [assignmentSingleCycleKernelSum_eq_factorial_mul_trace K m hm]
  calc
    ζ ^ (m - 1) * ((Nat.factorial (m - 1) : ℂ) * Matrix.trace (K ^ m)) /
          (Nat.factorial m : ℂ) =
        ζ ^ (m - 1) * Matrix.trace (K ^ m) *
          ((Nat.factorial (m - 1) : ℂ) / (Nat.factorial m : ℂ)) := by
      ring
    _ = ζ ^ (m - 1) * Matrix.trace (K ^ m) * (1 / (m : ℂ)) := by
      rw [factorial_pred_div_factorial_complex m hm]
    _ = ζ ^ (m - 1) * Matrix.trace (K ^ m) / (m : ℂ) := by
      rw [div_eq_mul_inv, one_div]

end Combinatorics

import LeanCondensedMatter.Combinatorics.PermutationSingleCycleKernel
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Assignment-summed single-cycle kernels

This file is the finite bridge from fixed-label single-cycle combinatorics to the trace coefficients
used later in W3 of the exchange/cumulant route.

The combinatorial labels are `Fin m`, while `x : Fin m → ι` assigns physical indices to those
labels. Repetitions are deliberately allowed. This distinction is what makes the later
`Matrix.trace (K ^ m)` identity correct.

This layer still stops before matrix traces: it packages the outer assignment sum and removes the
universal exchange factor. Cyclic enumeration and matrix algebra belong to the next layer.
-/

namespace Combinatorics

open Finset

variable {ι R : Type*} [Fintype ι]

/-- Sum the pure connected single-cycle kernel over all assignments of `m` abstract labels to the
physical index type `ι`. Assignments need not be injective. -/
noncomputable def assignmentSingleCycleKernelSum [CommSemiring R]
    (K : ι → ι → R) (m : ℕ) : R :=
  ∑ x : Fin m → ι,
    singleCycleKernelSum (fun a b : Fin m => K (x a) (x b)) Finset.univ

/-- After summing over all physical-index assignments, the exchange parameter remains a single
universal factor `ζ ^ (m - 1)`.

This is the W3.2 input for the later cyclic-enumeration theorem: the remaining assignment-summed
kernel is independent of `ζ`. -/
theorem sum_singleCycleContribution_assignments_eq_pow_mul_assignmentSingleCycleKernelSum
    [CommSemiring R] (ζ : R) (K : ι → ι → R) (m : ℕ) :
    (∑ x : Fin m → ι,
      singleCycleContribution ζ (fun a b : Fin m => K (x a) (x b)) Finset.univ) =
      ζ ^ (m - 1) * assignmentSingleCycleKernelSum K m := by
  classical
  simp_rw [singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum]
  simp [assignmentSingleCycleKernelSum, Finset.mul_sum]

end Combinatorics

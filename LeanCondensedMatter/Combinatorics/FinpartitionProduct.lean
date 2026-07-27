import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Products over the parts of a finite partition

These lemmas express a product over a finite set as an iterated product over the parts of a
`Finpartition`, and factor a power whose exponent is the cardinality of the underlying set into the
corresponding powers for each part.  They are pure finite combinatorics and commutative-monoid
algebra; no diagram, field-operator, or particle-statistics structure is involved.
-/

namespace Finpartition

variable {α M : Type*} [DecidableEq α] [CommMonoid M] {s : Finset α}

/-- A product over `s` is the iterated product over the parts of a finite partition of `s`. -/
theorem prod_eq_prod_parts (π : Finpartition s) (f : ↥s → M) :
    (∏ x : ↥s, f x) =
      ∏ B : π.parts, ∏ x : ↥(B : Finset α), f (π.equivSigmaParts.symm ⟨B, x⟩) := by
  classical
  calc
    (∏ x : ↥s, f x) =
        ∏ y : Σ B : π.parts, ↥(B : Finset α), f (π.equivSigmaParts.symm y) := by
      refine Fintype.prod_equiv π.equivSigmaParts f
        (fun y => f (π.equivSigmaParts.symm y)) ?_
      intro x
      simp
    _ = ∏ B : π.parts, ∏ x : ↥(B : Finset α), f (π.equivSigmaParts.symm ⟨B, x⟩) :=
      Fintype.prod_sigma _

/-- A power indexed by `s.card` factors into powers indexed by the cardinalities of the partition
parts. -/
theorem pow_card_eq_prod_parts (π : Finpartition s) (a : M) :
    a ^ s.card = ∏ B : π.parts, a ^ (B : Finset α).card := by
  classical
  rw [Finset.prod_coe_sort π.parts (fun B => a ^ B.card)]
  have hpow : ∀ T : Finset (Finset α),
      (∏ B ∈ T, a ^ B.card) = a ^ (∑ B ∈ T, B.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert B T hBT ih =>
      simp [hBT, ih, pow_add]
  rw [hpow, π.sum_card_parts]

end Finpartition

import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Products over the parts of a finite partition

These lemmas express a product over a finite set as an iterated product over the parts of a
`Finpartition`, and factor a power whose exponent is the cardinality of the underlying set into the
corresponding powers for each part. The mapped-subfinset equivalence also covers situations where
only one sector of a larger partitioned type is being decomposed. Everything here is pure finite
combinatorics and commutative-monoid algebra; no diagram, field-operator, or particle-statistics
structure is involved.
-/

namespace Finpartition

variable {α M : Type*} [DecidableEq α] [CommMonoid M] {s : Finset α}

/-- Decompose a finite source set into subfinsets classified by the parts of `π` after applying
`f`. The family `fiber B` may live in a different ambient type from the partition itself; it only
needs to describe exactly the source elements whose images lie in `B`. -/
noncomputable def equivSigmaSubfinsets {β : Type*}
    (π : Finpartition s) (t : Finset β) (f : ↥t → α)
    (hf : ∀ x, f x ∈ s)
    (fiber : π.parts → Finset β)
    (hfiber : ∀ B, fiber B ⊆ t)
    (hmem : ∀ (B : π.parts) (x : ↥t), (x : β) ∈ fiber B ↔ f x ∈ (B : Finset α)) :
    ↥t ≃ Σ B : π.parts, ↥(fiber B) :=
  (Equiv.sigmaFiberEquiv fun x : ↥t =>
      (⟨π.part (f x), (π.part_mem).2 (hf x)⟩ : π.parts)).symm.trans
    (Equiv.sigmaCongrRight fun B =>
      { toFun := fun x =>
          ⟨x.1.1, (hmem B x.1).2
            ((π.part_eq_iff_mem B.2).1 (congrArg Subtype.val x.2))⟩
        invFun := fun x =>
          ⟨⟨x.1, hfiber B x.2⟩, Subtype.ext
            ((π.part_eq_iff_mem B.2).2
              ((hmem B ⟨x.1, hfiber B x.2⟩).1 x.2))⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl })

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
  rw [Finset.prod_coe_sort π.parts (fun B => a ^ B.card),
    Finset.prod_pow_eq_pow_sum, π.sum_card_parts]

end Finpartition

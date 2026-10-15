import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.BigOperators
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct

set_option linter.style.header false

/-!
# Products over the parts of a finite partition

This module owns `partitionProduct`, the product of a finite-set function over partition blocks,
its top-partition evaluation, and its multiplicativity under `bind`.

The remaining lemmas express a product over a finite set as an iterated product over the parts of a
`Finpartition`, and factor a power whose exponent is the cardinality of the underlying set into the
corresponding powers for each part. The mapped-subfinset equivalence also covers situations where
only one sector of a larger partitioned type is being decomposed. Everything here is pure finite
combinatorics and commutative-monoid algebra; no diagram, field-operator, or particle-statistics
structure is involved.
-/

namespace Finpartition

variable {α M : Type*} [DecidableEq α] [CommMonoid M] {s : Finset α}

/-- Product of `f` over the blocks of a partition. -/
noncomputable def partitionProduct (f : Finset α → M) {S : Finset α} (π : Finpartition S) : M :=
  ∏ B ∈ π.parts, f B

@[simp]
theorem partitionProduct_top {S : Finset α} (hS : S ≠ ∅) (f : Finset α → M) :
    partitionProduct f (⊤ : Finpartition S) = f S := by
  have hparts : (⊤ : Finpartition S).parts = {S} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?_, fun d hd => Finset.mem_singleton.1 (Finpartition.parts_top_subset S hd)⟩
    obtain ⟨x, hx⟩ := (Finpartition.parts_nonempty_iff (P := (⊤ : Finpartition S))).2 hS
    rwa [Finset.mem_singleton.1 (Finpartition.parts_top_subset S hx)] at hx
  rw [partitionProduct, hparts, Finset.prod_singleton]

/-- Block products factor over a partition constructed by `bind`. -/
theorem partitionProduct_bind (f : Finset α → M) {S : Finset α} (σ : Finpartition S)
    (Q : ∀ B ∈ σ.parts, Finpartition B) :
    partitionProduct f (σ.bind Q) = ∏ B ∈ σ.parts.attach, partitionProduct f (Q B.1 B.2) := by
  classical
  change ∏ C ∈ (σ.bind Q).parts, f C = _
  apply Finset.prod_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun, Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne, Subtype.mk_eq_mk] at hbc
  exact (Q b hb).ne_bot hdb
    (eq_bot_iff.2 <| (le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans <|
      (σ.disjoint hb hc hbc).le_bot)

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

/-- A power indexed by `s.card` factors into powers indexed by the cardinalities of the partition
parts. -/
theorem pow_card_eq_prod_parts (π : Finpartition s) (a : M) :
    a ^ s.card = ∏ B : π.parts, a ^ (B : Finset α).card := by
  classical
  rw [Finset.prod_coe_sort π.parts (fun B => a ^ B.card),
    Finset.prod_pow_eq_pow_sum, π.sum_card_parts]

end Finpartition

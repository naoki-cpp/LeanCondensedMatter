import LeanCondensedMatter.Combinatorics.Shuffle.FamilyOrderShuffle
import LeanCondensedMatter.Combinatorics.Shuffle.FamilySlotShuffleInversions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false

/-!
# Orders and shuffles over finite partitions

A global ordering of a finite set canonically decomposes into an ordering on every part of a finite
partition together with an order-preserving shuffle of the part-local slots.  This module contains
only the finite combinatorics of that decomposition; no diagram, graph, or particle-statistics
structure is involved.
-/

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- An ordering of the elements in every part of a finite partition. -/
abbrev PartOrders (π : Finpartition s) :=
  Combinatorics.FamilyOrdersOf
    (fun B : π.parts => ↥(B : Finset α))
    (fun B : π.parts => (B : Finset α).card)

/-- An order-preserving interleaving of all part-local slots into the ambient slots. -/
abbrev PartShuffle (π : Finpartition s) :=
  Combinatorics.FamilySlotShuffleTo
    (fun B : π.parts => (B : Finset α).card) s.card

/-- The disjoint union of part-local slots, identified with the ambient finite set using the chosen
local order on every part. -/
noncomputable def partEquiv (π : Finpartition s) (orders : π.PartOrders) :
    (Σ B : π.parts, Fin (B : Finset α).card) ≃ ↥s :=
  (Equiv.sigmaCongrRight fun B => orders B).trans π.equivSigmaParts.symm

/-- Assemble a global order from part-local orders and an order-preserving shuffle. -/
noncomputable def assembleOrder (π : Finpartition s) (orders : π.PartOrders)
    (shuffle : π.PartShuffle) : Fin s.card ≃ ↥s :=
  Combinatorics.assembleFamilyOrderOfSize
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    π.equivSigmaParts orders shuffle

/-- A family of part-local orders is compatible with a global order when every part appears in the
ambient slots in precisely that local order. -/
noncomputable def PartOrdersCompatible (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) : Prop :=
  ∀ B, StrictMono (fun i => order.symm (π.partEquiv orders ⟨B, i⟩))

/-- Read off the unique part shuffle from a global order and compatible part-local orders. -/
noncomputable def shuffleOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders) : π.PartShuffle where
  slotEquiv := (π.partEquiv orders).trans order.symm
  strictMono := h

/-- The slots occupied by a partition block under the shuffle extracted from
a global order are exactly the ambient positions whose elements belong to
that block. This depends only on finite-set combinatorics, not on statistics. -/
theorem mem_shuffleOfOrder_blockSlotSet_iff
    (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders)
    (B : π.parts) (x : Fin s.card) :
    x ∈ (π.shuffleOfOrder order orders h).blockSlotSet B ↔
      (order x).1 ∈ (B : Finset α) := by
  classical
  simp only [Combinatorics.FamilySlotShuffleTo.blockSlotSet,
    Finset.mem_image, Finset.mem_univ, true_and]
  change (∃ i : Fin (B : Finset α).card,
      order.symm (π.partEquiv orders ⟨B, i⟩) = x) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : (π.partEquiv orders ⟨B, i⟩).1 ∈ (B : Finset α) :=
      (orders B i).2
    simpa only [Equiv.apply_symm_apply] using hmem
  · intro hx
    refine ⟨(orders B).symm ⟨(order x).1, hx⟩, ?_⟩
    apply order.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (orders B ((orders B).symm ⟨(order x).1, hx⟩)).1 = (order x).1
    simp

/-- The local orders used to assemble a global order are compatible with that assembled order. -/
theorem partOrdersCompatible_assembleOrder (π : Finpartition s) (orders : π.PartOrders)
    (shuffle : π.PartShuffle) :
    π.PartOrdersCompatible (π.assembleOrder orders shuffle) orders := by
  intro B
  have hslot (i : Fin (B : Finset α).card) :
      (π.assembleOrder orders shuffle).symm (π.partEquiv orders ⟨B, i⟩) =
        shuffle.slotEquiv ⟨B, i⟩ := by
    simpa [Finpartition.assembleOrder, Finpartition.partEquiv] using
      (Combinatorics.assembleFamilyOrderOfSize_symm_apply
        (F := fun B : π.parts => ↥(B : Finset α))
        (size := fun B : π.parts => (B : Finset α).card)
        π.equivSigmaParts orders shuffle B i)
  intro i j hij
  simpa only [hslot i, hslot j] using shuffle.strictMono B hij

/-- Reassembling a global order from compatible part-local orders and its extracted shuffle is the
original global order. -/
@[simp]
theorem assembleOrder_shuffleOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s)
    (orders : π.PartOrders) (h : π.PartOrdersCompatible order orders) :
    π.assembleOrder orders (π.shuffleOfOrder order orders h) = order := by
  apply Combinatorics.assembleFamilyOrderOfSize_eq_order
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    π.equivSigmaParts orders (π.shuffleOfOrder order orders h) order
  intro B j
  rfl

/-- The canonical family of part-local orders induced by an ambient order. -/
noncomputable def partOrdersOfOrder (π : Finpartition s) (order : Fin s.card ≃ ↥s) :
    π.PartOrders :=
  Combinatorics.familyOrdersOfOrder
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    (hcard := fun B => Fintype.card_coe (B : Finset α))
    π.equivSigmaParts order

/-- The canonical part-local orders are compatible with the ambient order. -/
theorem partOrdersCompatible_partOrdersOfOrder (π : Finpartition s)
    (order : Fin s.card ≃ ↥s) :
    π.PartOrdersCompatible order (π.partOrdersOfOrder order) := by
  intro B
  simpa only [Finpartition.PartOrdersCompatible, Finpartition.partEquiv,
    Finpartition.partOrdersOfOrder, Equiv.trans_apply, Equiv.sigmaCongrRight_apply] using
    (Combinatorics.familyOrdersOfOrder_strictMono
      (F := fun B : π.parts => ↥(B : Finset α))
      (size := fun B : π.parts => (B : Finset α).card)
      (hcard := fun B => Fintype.card_coe (B : Finset α))
      π.equivSigmaParts order B)

/-- The canonical partition shuffle preserves the increasing order of
elements within each block. -/
noncomputable def shuffleOfIncreasingOrder [LinearOrder α]
    (π : Finpartition s) : π.PartShuffle := by
  let order := (s.orderIsoOfFin rfl).toEquiv
  exact π.shuffleOfOrder order (π.partOrdersOfOrder order)
    (π.partOrdersCompatible_partOrdersOfOrder order)

/-- For a partition of the full `Fin n` family, the canonical increasing
shuffle occupies precisely the slots belonging to each block. -/
theorem shuffleOfIncreasingOrderFull_blockSlotSet
    {n : ℕ} (π : Finpartition (Finset.univ : Finset (Fin n)))
    (B : π.parts) :
    ((Combinatorics.FamilySlotShuffleTo.castTotalEquiv (by simp))
      π.shuffleOfIncreasingOrder).blockSlotSet B =
        (B : Finset (Fin n)) := by
  classical
  let s : Finset (Fin n) := Finset.univ
  let o : Fin s.card ≃ ↥s := (s.orderIsoOfFin rfl).toEquiv
  let hcard : s.card = n := by simp [s]
  let idIso : Fin n ≃o ↥s := {
    toEquiv := {
      toFun := fun x => ⟨x, Finset.mem_univ x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun x => Subtype.ext rfl
    }
    map_rel_iff' := by intro x y; rfl
  }
  let canonical := (Fin.castOrderIso hcard).trans idIso
  have heq : (s.orderIsoOfFin rfl) = canonical := Subsingleton.elim _ _
  have ho (i : Fin s.card) : (o i).1 = Fin.cast hcard i := by
    change ((s.orderIsoOfFin rfl) i).1 = Fin.cast hcard i
    rw [heq]
    rfl
  ext x
  change x ∈ ((Combinatorics.FamilySlotShuffleTo.castTotalEquiv hcard)
      (π.shuffleOfOrder o (π.partOrdersOfOrder o)
        (π.partOrdersCompatible_partOrdersOfOrder o))).blockSlotSet B ↔
    x ∈ (B : Finset (Fin n))
  rw [(π.shuffleOfOrder o (π.partOrdersOfOrder o)
      (π.partOrdersCompatible_partOrdersOfOrder o)).mem_castTotalEquiv_blockSlotSet_iff
        hcard B x,
    π.mem_shuffleOfOrder_blockSlotSet_iff o (π.partOrdersOfOrder o)
      (π.partOrdersCompatible_partOrdersOfOrder o) B]
  have hx : (o (Fin.cast hcard.symm x)).1 = x := by
    rw [ho]
    apply Fin.ext
    rfl
  rw [hx]

/-- A global finite-set order is equivalent to part-local orders together with an order-preserving
shuffle of their slots. -/
noncomputable def orderDecompositionEquiv (π : Finpartition s) :
    (Fin s.card ≃ ↥s) ≃ π.PartOrders × π.PartShuffle :=
  Combinatorics.familyOrderDecompositionEquivOfSize
    (F := fun B : π.parts => ↥(B : Finset α))
    (size := fun B : π.parts => (B : Finset α).card)
    (hcard := fun B => Fintype.card_coe (B : Finset α))
    π.equivSigmaParts

/-- Summing a weight over all global orders factors through component-local order sums whenever,
for each fixed family of local orders, the shuffle sum is a common scalar times the product of
the corresponding local weights. -/
theorem sum_order_eq_mul_prod_sum_partOrders
    {R : Type*} [CommSemiring R]
    (π : Finpartition s)
    (globalWeight : (Fin s.card ≃ ↥s) → R)
    (localWeight :
      ∀ B : π.parts, (Fin (B : Finset α).card ≃ ↥(B : Finset α)) → R)
    (c : R)
    (hshuffle : ∀ orders : π.PartOrders,
      (∑ shuffle : π.PartShuffle, globalWeight (π.assembleOrder orders shuffle)) =
        c * ∏ B : π.parts, localWeight B (orders B)) :
    (∑ order : Fin s.card ≃ ↥s, globalWeight order) =
      c * ∏ B : π.parts,
        ∑ order : Fin (B : Finset α).card ≃ ↥(B : Finset α),
          localWeight B order := by
  classical
  calc
    (∑ order : Fin s.card ≃ ↥s, globalWeight order) =
        ∑ x : π.PartOrders × π.PartShuffle,
          globalWeight (π.assembleOrder x.1 x.2) := by
      rw [← Equiv.sum_comp (π.orderDecompositionEquiv).symm]
      rfl
    _ = ∑ orders : π.PartOrders,
          ∑ shuffle : π.PartShuffle,
            globalWeight (π.assembleOrder orders shuffle) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ orders : π.PartOrders,
          c * ∏ B : π.parts, localWeight B (orders B) := by
      apply Fintype.sum_congr
      intro orders
      exact hshuffle orders
    _ = c * ∑ orders : π.PartOrders,
          ∏ B : π.parts, localWeight B (orders B) := by
      rw [Finset.mul_sum]
    _ = c * ∏ B : π.parts,
          ∑ order : Fin (B : Finset α).card ≃ ↥(B : Finset α),
            localWeight B order := by
      congr 1
      simpa using
        (Finset.prod_univ_sum
          (fun B : π.parts =>
            (Finset.univ :
              Finset (Fin (B : Finset α).card ≃ ↥(B : Finset α))))
          localWeight).symm

end Finpartition

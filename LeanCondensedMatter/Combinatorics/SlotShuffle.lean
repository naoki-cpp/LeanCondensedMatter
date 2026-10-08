import LeanCondensedMatter.Combinatorics.SumEquivPartition
import LeanCondensedMatter.Combinatorics.SubsetSplit
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum

set_option linter.style.header false

/-!
# Order-preserving ambient slot shuffles

A `SlotShuffle m n` interleaves two ordered slot families through an ambient equivalence. Its
left slots determine it uniquely: increasing enumeration of a left-slot set and its complement
constructs the inverse correspondence directly, independently of any recursive shuffle presentation.
-/

namespace Combinatorics

open scoped BigOperators

/-- An order-preserving equivalence of two local slot families with the ambient slots. -/
structure SlotShuffle (m n : ℕ) where
  /-- Equivalence between tagged local slots and ambient slots. -/
  slotEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)
  strictMonoLeft : StrictMono (fun i => slotEquiv (Sum.inl i))
  strictMonoRight : StrictMono (fun j => slotEquiv (Sum.inr j))

/-- Two ambient slot shuffles are equal when their slot equivalences are equal. -/
@[ext]
theorem SlotShuffle.ext {m n : ℕ} {σ τ : SlotShuffle m n}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Ambient slot shuffles form a finite type. -/
noncomputable instance SlotShuffle.instFintype (m n : ℕ) : Fintype (SlotShuffle m n) :=
  Fintype.ofInjective (fun σ : SlotShuffle m n => σ.slotEquiv)
    (fun _ _ h => SlotShuffle.ext h)

/-- Ambient positions occupied by the left local slots. -/
def SlotShuffle.leftSlots {m n : ℕ} (σ : SlotShuffle m n) : Finset (Fin (m + n)) :=
  SumEquiv.leftImage σ.slotEquiv

/-- Ambient positions occupied by the right local slots. -/
def SlotShuffle.rightSlots {m n : ℕ} (σ : SlotShuffle m n) : Finset (Fin (m + n)) :=
  SumEquiv.rightImage σ.slotEquiv

@[simp]
theorem SlotShuffle.card_leftSlots {m n : ℕ} (σ : SlotShuffle m n) :
    σ.leftSlots.card = m := by
  simpa [SlotShuffle.leftSlots] using (SumEquiv.card_leftImage σ.slotEquiv)

@[simp]
theorem SlotShuffle.card_rightSlots {m n : ℕ} (σ : SlotShuffle m n) :
    σ.rightSlots.card = n := by
  simpa [SlotShuffle.rightSlots] using (SumEquiv.card_rightImage σ.slotEquiv)

@[simp]
theorem SlotShuffle.mem_leftSlots_iff {m n : ℕ} (σ : SlotShuffle m n)
    (x : Fin (m + n)) :
    x ∈ σ.leftSlots ↔ ∃ i : Fin m, σ.slotEquiv (Sum.inl i) = x := by
  simpa [SlotShuffle.leftSlots] using (SumEquiv.mem_leftImage_iff σ.slotEquiv x)

/-- The increasing enumeration of the left slots is the left shuffle slot map. -/
theorem SlotShuffle.leftSlots_orderEmbOfFin {m n : ℕ}
    (σ : SlotShuffle m n) (i : Fin m) :
    σ.leftSlots.orderEmbOfFin σ.card_leftSlots i =
      σ.slotEquiv (Sum.inl i) := by
  have h := Finset.orderEmbOfFin_unique
    (s := σ.leftSlots) (h := σ.card_leftSlots)
    (f := fun q => σ.slotEquiv (Sum.inl q))
    (fun q => (σ.mem_leftSlots_iff _).2 ⟨q, rfl⟩)
    σ.strictMonoLeft
  exact congrFun h.symm i

@[simp]
theorem SlotShuffle.mem_rightSlots_iff {m n : ℕ} (σ : SlotShuffle m n)
    (x : Fin (m + n)) :
    x ∈ σ.rightSlots ↔ ∃ j : Fin n, σ.slotEquiv (Sum.inr j) = x := by
  simpa [SlotShuffle.rightSlots] using (SumEquiv.mem_rightImage_iff σ.slotEquiv x)

/-- The right slots are precisely the complement of the left slots. -/
theorem SlotShuffle.mem_rightSlots_iff_not_mem_leftSlots {m n : ℕ}
    (σ : SlotShuffle m n) (x : Fin (m + n)) :
    x ∈ σ.rightSlots ↔ x ∉ σ.leftSlots := by
  simpa [SlotShuffle.leftSlots, SlotShuffle.rightSlots] using
    (SumEquiv.mem_rightImage_iff_not_mem_leftImage σ.slotEquiv x)

/-- The complement of the left slots has the right perturbation order. -/
@[simp]
theorem SlotShuffle.card_sdiff_leftSlots {m n : ℕ} (σ : SlotShuffle m n) :
    ((Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots).card = n := by
  have hright :
      (Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots = σ.rightSlots := by
    simpa [SlotShuffle.leftSlots, SlotShuffle.rightSlots] using
      (SumEquiv.rightImage_eq_sdiff_leftImage σ.slotEquiv).symm
  rw [hright, σ.card_rightSlots]

/-- The increasing enumeration of the complement of the left slots is the right slot map. -/
theorem SlotShuffle.sdiffLeftSlots_orderEmbOfFin {m n : ℕ}
    (σ : SlotShuffle m n) (j : Fin n) :
    ((Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots).orderEmbOfFin
        σ.card_sdiff_leftSlots j =
      σ.slotEquiv (Sum.inr j) := by
  have h := Finset.orderEmbOfFin_unique
    (s := (Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots)
    (h := σ.card_sdiff_leftSlots)
    (f := fun q => σ.slotEquiv (Sum.inr q))
    (fun q => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact (σ.mem_rightSlots_iff_not_mem_leftSlots _).1
        ((σ.mem_rightSlots_iff _).2 ⟨q, rfl⟩))
    σ.strictMonoRight
  exact congrFun h.symm j

/-- The local right slots identified with the ambient complement of the left slots in increasing
order. -/
noncomputable def SlotShuffle.sdiffLeftSlotsOrderEquiv {m n : ℕ}
    (σ : SlotShuffle m n) :
    Fin n ≃ ↥((Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots) :=
  (((Finset.univ : Finset (Fin (m + n))) \ σ.leftSlots).orderIsoOfFin
    σ.card_sdiff_leftSlots).toEquiv

/-- A slot shuffle is uniquely determined by the ambient positions of its left slots. -/
theorem SlotShuffle.eq_of_leftSlots_eq {m n : ℕ} {σ τ : SlotShuffle m n}
    (hslots : σ.leftSlots = τ.leftSlots) : σ = τ := by
  apply SlotShuffle.ext
  apply Equiv.ext
  intro x
  cases x with
  | inl i =>
      have hσ := Finset.orderEmbOfFin_unique
        (s := σ.leftSlots) (h := σ.card_leftSlots)
        (f := fun k => σ.slotEquiv (Sum.inl k))
        (fun k => (σ.mem_leftSlots_iff _).2 ⟨k, rfl⟩) σ.strictMonoLeft
      have hτ := Finset.orderEmbOfFin_unique
        (s := σ.leftSlots) (h := σ.card_leftSlots)
        (f := fun k => τ.slotEquiv (Sum.inl k))
        (fun k => by
          rw [hslots]
          exact (τ.mem_leftSlots_iff _).2 ⟨k, rfl⟩) τ.strictMonoLeft
      exact congrFun (hσ.trans hτ.symm) i
  | inr j =>
      have hright : σ.rightSlots = τ.rightSlots := by
        ext x
        rw [σ.mem_rightSlots_iff_not_mem_leftSlots,
          τ.mem_rightSlots_iff_not_mem_leftSlots, hslots]
      have hσ := Finset.orderEmbOfFin_unique
        (s := σ.rightSlots) (h := σ.card_rightSlots)
        (f := fun k => σ.slotEquiv (Sum.inr k))
        (fun k => (σ.mem_rightSlots_iff _).2 ⟨k, rfl⟩) σ.strictMonoRight
      have hτ := Finset.orderEmbOfFin_unique
        (s := σ.rightSlots) (h := σ.card_rightSlots)
        (f := fun k => τ.slotEquiv (Sum.inr k))
        (fun k => by
          rw [hright]
          exact (τ.mem_rightSlots_iff _).2 ⟨k, rfl⟩) τ.strictMonoRight
      exact congrFun (hσ.trans hτ.symm) j

/-- The type of possible ambient left-slot sets. -/
abbrev LeftSlotSet (m n : ℕ) :=
  {s : Finset (Fin (m + n)) // s.card = m}

/-- Record only the ambient set occupied by the left family. -/
def SlotShuffle.toLeftSlotSet {m n : ℕ} (σ : SlotShuffle m n) : LeftSlotSet m n :=
  ⟨σ.leftSlots, σ.card_leftSlots⟩

/-- The left-slot set determines the whole slot shuffle. -/
theorem SlotShuffle.toLeftSlotSet_injective {m n : ℕ} :
    Function.Injective (SlotShuffle.toLeftSlotSet : SlotShuffle m n → LeftSlotSet m n) := by
  intro σ τ h
  apply SlotShuffle.eq_of_leftSlots_eq
  exact congrArg Subtype.val h

/-- The possible left-slot sets are counted by a binomial coefficient. -/
theorem card_leftSlotSet (m n : ℕ) :
    Fintype.card (LeftSlotSet m n) = Nat.choose (m + n) m := by
  classical
  change Fintype.card {s : Finset (Fin (m + n)) // s.card = m} = Nat.choose (m + n) m
  let e : {s : Finset (Fin (m + n)) // s.card = m} ≃
      ↥((Finset.univ : Finset (Fin (m + n))).powersetCard m) :=
    Equiv.subtypeEquivRight fun s => by
      simp [Finset.mem_powersetCard]
  rw [Fintype.card_congr e]
  simp

private theorem card_leftSlotSet_complement {m n : ℕ} (s : LeftSlotSet m n) :
    ((Finset.univ : Finset (Fin (m + n))) \ s.1).card = n := by
  simp [Finset.card_sdiff, s.2]

/-- Enumerate a left-slot set and its complement increasingly. -/
private noncomputable def SlotShuffle.ofLeftSlotSet {m n : ℕ} (s : LeftSlotSet m n) :
    SlotShuffle m n where
  slotEquiv :=
    (Equiv.sumCongr (s.1.orderIsoOfFin s.2).toEquiv
      (((Finset.univ : Finset (Fin (m + n))) \ s.1).orderIsoOfFin
        (card_leftSlotSet_complement s)).toEquiv).trans
      ((subsetSumSdiffEquiv (Finset.subset_univ s.1)).trans
        (Equiv.subtypeUnivEquiv (fun x : Fin (m + n) => Finset.mem_univ x)))
  strictMonoLeft := by
    intro i j hij
    exact (s.1.orderIsoOfFin s.2).strictMono hij
  strictMonoRight := by
    intro i j hij
    exact (((Finset.univ : Finset (Fin (m + n))) \ s.1).orderIsoOfFin
      (card_leftSlotSet_complement s)).strictMono hij

private theorem SlotShuffle.ofLeftSlotSet_leftSlots {m n : ℕ} (s : LeftSlotSet m n) :
    (SlotShuffle.ofLeftSlotSet s).leftSlots = s.1 := by
  ext x
  rw [(SlotShuffle.ofLeftSlotSet s).mem_leftSlots_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.1.orderIsoOfFin s.2 i).2
  · intro hx
    refine ⟨(s.1.orderIsoOfFin s.2).symm ⟨x, hx⟩, ?_⟩
    change ((s.1.orderIsoOfFin s.2 ((s.1.orderIsoOfFin s.2).symm ⟨x, hx⟩) : ↥s.1) :
      Fin (m + n)) = x
    simp

/-- Ambient slot shuffles are equivalent to their ambient left-slot sets. -/
noncomputable def slotShuffleLeftSlotSetEquiv (m n : ℕ) :
    SlotShuffle m n ≃ LeftSlotSet m n where
  toFun := SlotShuffle.toLeftSlotSet
  invFun := SlotShuffle.ofLeftSlotSet
  left_inv σ := SlotShuffle.eq_of_leftSlots_eq (SlotShuffle.ofLeftSlotSet_leftSlots σ.toLeftSlotSet)
  right_inv s := Subtype.ext (SlotShuffle.ofLeftSlotSet_leftSlots s)

@[simp]
theorem slotShuffleLeftSlotSetEquiv_apply {m n : ℕ} (σ : SlotShuffle m n) :
    slotShuffleLeftSlotSetEquiv m n σ = σ.toLeftSlotSet := rfl

/-- Ambient slot shuffles have the binomial cardinality of their left-slot sets. -/
theorem SlotShuffle.card_eq_choose (m n : ℕ) :
    Fintype.card (SlotShuffle m n) = Nat.choose (m + n) m := by
  rw [Fintype.card_congr (slotShuffleLeftSlotSetEquiv m n), card_leftSlotSet]

/-- Reindex a finite sum over left-slot sets by ambient slot shuffles. -/
theorem sum_leftSlotSet [AddCommMonoid M] (m n : ℕ) (F : LeftSlotSet m n → M) :
    ∑ s : LeftSlotSet m n, F s =
      ∑ σ : SlotShuffle m n, F σ.toLeftSlotSet := by
  simpa using (Equiv.sum_comp (slotShuffleLeftSlotSetEquiv m n) F).symm

end Combinatorics

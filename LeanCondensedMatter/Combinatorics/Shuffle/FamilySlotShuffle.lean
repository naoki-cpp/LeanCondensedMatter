import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Fin.Basic

set_option linter.style.header false

/-!
# Order-preserving shuffles of a finite family of slot blocks

`FamilySlotShuffleTo size total` interleaves one ordered block `Fin (size i)` for every index `i`
into `Fin total`, preserving the order inside each block.  The canonical `FamilySlotShuffle size`
specializes the ambient cardinality to `∑ i, size i` when the index type is finite.

This module owns the shuffle structure, finite instances, index reindexing, and cardinality transport.
Inter-block inversion counts live in `FamilySlotShuffleInversions`; permutation signs live in
`FamilySlotShuffleSign`. Shuffled integrands and continuity live in
`Analysis/OrderedSimplex/FamilyShuffleIntegrand.lean`.
-/

open scoped BigOperators

namespace Combinatorics

variable {ι : Type*}

/-- An order-preserving interleaving of a family of local slot blocks into `Fin total`. -/
structure FamilySlotShuffleTo (size : ι → ℕ) (total : ℕ) where
  /-- Equivalence between tagged local slots and ambient slots. -/
  slotEquiv : (Σ i : ι, Fin (size i)) ≃ Fin total
  strictMono : ∀ i, StrictMono (fun j => slotEquiv ⟨i, j⟩)

@[ext]
theorem FamilySlotShuffleTo.ext {size : ι → ℕ} {total : ℕ}
    {σ τ : FamilySlotShuffleTo size total}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Ambient family shuffles form a finite type when the block index type is finite. -/
noncomputable instance FamilySlotShuffleTo.instFintype [Fintype ι]
    (size : ι → ℕ) (total : ℕ) : Fintype (FamilySlotShuffleTo size total) := by
  classical
  exact Fintype.ofInjective (fun shuffle : FamilySlotShuffleTo size total => shuffle.slotEquiv)
    (fun _ _ h => FamilySlotShuffleTo.ext h)

/-- Transport only the ambient finite cardinality of a family shuffle. -/
noncomputable def FamilySlotShuffleTo.castTotalEquiv {size : ι → ℕ} {m n : ℕ} (h : m = n) :
    FamilySlotShuffleTo size m ≃ FamilySlotShuffleTo size n where
  toFun shuffle :=
    { slotEquiv := shuffle.slotEquiv.trans (Fin.castOrderIso h).toEquiv
      strictMono := by
        intro i a b hab
        exact (Fin.castOrderIso h).strictMono (shuffle.strictMono i hab) }
  invFun shuffle :=
    { slotEquiv := shuffle.slotEquiv.trans (Fin.castOrderIso h).symm.toEquiv
      strictMono := by
        intro i a b hab
        exact (Fin.castOrderIso h).symm.strictMono (shuffle.strictMono i hab) }
  left_inv shuffle := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    intro x
    change Fin.cast h.symm (Fin.cast h (shuffle.slotEquiv x)) = shuffle.slotEquiv x
    simp
  right_inv shuffle := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    intro x
    change Fin.cast h (Fin.cast h.symm (shuffle.slotEquiv x)) = shuffle.slotEquiv x
    simp

/-- A family shuffle whose ambient cardinality is exactly the sum of its local block sizes. -/
abbrev FamilySlotShuffle [Fintype ι] (size : ι → ℕ) :=
  FamilySlotShuffleTo size (∑ i, size i)

section Reindex

variable {κ : Type*} [Fintype ι] [Fintype κ]

/-- Reindex family slot shuffles along an equivalence of their finite block-index types. -/
noncomputable def FamilySlotShuffle.reindexEquiv (e : ι ≃ κ) (size : κ → ℕ) :
    FamilySlotShuffle size ≃ FamilySlotShuffle (fun i => size (e i)) := by
  let hsum : (∑ i : ι, size (e i)) = ∑ j : κ, size j := Equiv.sum_comp e size
  let localEquiv : (Σ i : ι, Fin (size (e i))) ≃ (Σ j : κ, Fin (size j)) :=
    e.sigmaCongrLeft (β := fun j : κ => Fin (size j))
  exact
    { toFun := fun shuffle =>
        { slotEquiv := localEquiv.trans (shuffle.slotEquiv.trans (finCongr hsum.symm))
          strictMono := by
            intro i a b hab
            change (finCongr hsum.symm)
                (shuffle.slotEquiv (localEquiv ⟨i, a⟩)) <
              (finCongr hsum.symm)
                (shuffle.slotEquiv (localEquiv ⟨i, b⟩))
            simpa [localEquiv] using
              (Fin.castOrderIso hsum.symm).strictMono
                (shuffle.strictMono (e i) hab) }
      invFun := fun shuffle =>
        { slotEquiv := localEquiv.symm.trans (shuffle.slotEquiv.trans (finCongr hsum))
          strictMono := by
            intro j
            obtain ⟨i, rfl⟩ := e.surjective j
            intro a b hab
            have ha : localEquiv.symm ⟨e i, a⟩ = ⟨i, a⟩ := by
              apply localEquiv.injective
              simp [localEquiv]
            have hb : localEquiv.symm ⟨e i, b⟩ = ⟨i, b⟩ := by
              apply localEquiv.injective
              simp [localEquiv]
            change (finCongr hsum)
                (shuffle.slotEquiv (localEquiv.symm ⟨e i, a⟩)) <
              (finCongr hsum)
                (shuffle.slotEquiv (localEquiv.symm ⟨e i, b⟩))
            rw [ha, hb]
            exact (Fin.castOrderIso hsum).strictMono
              (shuffle.strictMono i hab) }
      left_inv := by
        intro shuffle
        apply FamilySlotShuffleTo.ext
        apply Equiv.ext
        intro x
        simp [localEquiv]
      right_inv := by
        intro shuffle
        apply FamilySlotShuffleTo.ext
        apply Equiv.ext
        intro x
        change (finCongr hsum.symm)
            ((finCongr hsum) (shuffle.slotEquiv (localEquiv.symm (localEquiv x)))) =
          shuffle.slotEquiv x
        rw [localEquiv.symm_apply_apply]
        simp }

end Reindex

/-- The unique shuffle of an empty family of slot blocks. -/
noncomputable def FamilySlotShuffle.nil (size : Fin 0 → ℕ) : FamilySlotShuffle size where
  slotEquiv := Fintype.equivOfCardEq (by simp)
  strictMono := fun i => Fin.elim0 i

/-- A shuffle of an empty family is unique. -/
noncomputable instance FamilySlotShuffle.instUniqueZero (size : Fin 0 → ℕ) :
    Unique (FamilySlotShuffle size) where
  default := FamilySlotShuffle.nil size
  uniq shuffle := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    rintro ⟨i, _⟩
    exact Fin.elim0 i


/-- Relabel ambient interaction slots from one shuffle of a fixed
family of local slot sizes to another. The local block identifier and
local slot index are unchanged; only their ambient positions move. -/
def FamilySlotShuffleTo.ambientRelabel
    {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) :
    Fin total ≃ Fin total :=
  σ.slotEquiv.symm.trans τ.slotEquiv

/-- The ambient relabeling takes each exact source local slot to the
same local slot in the target shuffle, including empty fibers. -/
@[simp]
theorem FamilySlotShuffleTo.ambientRelabel_apply_slot
    {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total)
    (v : Σ i, Fin (size i)) :
    (σ.ambientRelabel τ) (σ.slotEquiv v) = τ.slotEquiv v := by
  simp [FamilySlotShuffleTo.ambientRelabel]

/-- The relabeling preserves the *physical owner* of every ambient slot.
This lets the same standardized local Wick diagrams be carried through
different physical interaction-owner assignments. -/
theorem FamilySlotShuffleTo.ambientRelabel_owner
    {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total)
    (v : Fin total) :
    (τ.slotEquiv.symm (σ.ambientRelabel τ v)).1 =
      (σ.slotEquiv.symm v).1 := by
  simp [FamilySlotShuffleTo.ambientRelabel]


/-- A fixed local owner fiber is relabeled in increasing order by the
permutation between two order-preserving family shuffles. This is
stronger than owner preservation: it identifies local increasing
enumerations without an extra within-block permutation. -/
theorem FamilySlotShuffleTo.ambientRelabel_strictMono_ownerFiber
    {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) (i : ι) :
    StrictMono (fun v : {v : Fin total // (σ.slotEquiv.symm v).1 = i} =>
      σ.ambientRelabel τ v.1) := by
  have hrepr (v : {v : Fin total // (σ.slotEquiv.symm v).1 = i}) :
      ∃ j : Fin (size i), v.1 = σ.slotEquiv ⟨i, j⟩ := by
    rcases hq : σ.slotEquiv.symm v.1 with ⟨i', j⟩
    have hi : i' = i := by
      simpa [hq] using v.2
    subst i'
    refine ⟨j, ?_⟩
    calc
      v.1 = σ.slotEquiv (σ.slotEquiv.symm v.1) :=
        (σ.slotEquiv.apply_symm_apply _).symm
      _ = σ.slotEquiv ⟨i, j⟩ := congrArg σ.slotEquiv hq
  intro a b hab
  obtain ⟨ja, ha⟩ := hrepr a
  obtain ⟨jb, hb⟩ := hrepr b
  change a.1 < b.1 at hab
  rw [ha, hb] at hab
  have hj : ja < jb := by
    by_contra h
    have hle : jb ≤ ja := le_of_not_gt h
    have hrev : σ.slotEquiv ⟨i, jb⟩ ≤ σ.slotEquiv ⟨i, ja⟩ :=
      (σ.strictMono i).monotone hle
    exact (not_le_of_gt hab) hrev
  change (σ.ambientRelabel τ) a.1 < (σ.ambientRelabel τ) b.1
  rw [ha, hb, σ.ambientRelabel_apply_slot, σ.ambientRelabel_apply_slot]
  exact (τ.strictMono i) hj


/-- Relabel the *names* of the blocks in an order-preserving
shuffle without changing any ambient slot. Unlike reindexing a shuffle
with an ambient size equal to a finite sum, this works for an arbitrary
fixed ambient cardinality and introduces no cast on the global slots. -/
noncomputable def FamilySlotShuffleTo.reindexEquiv
    {κ : Type*} (e : ι ≃ κ) (size : κ → ℕ) {total : ℕ} :
    FamilySlotShuffleTo size total ≃
      FamilySlotShuffleTo (fun i => size (e i)) total where
  toFun σ :=
    { slotEquiv := (e.sigmaCongrLeft (β := fun j => Fin (size j))).trans σ.slotEquiv
      strictMono := by
        intro i a b hab
        simpa [Equiv.sigmaCongrLeft, Equiv.trans_apply] using σ.strictMono (e i) hab }
  invFun τ :=
    { slotEquiv :=
        (e.sigmaCongrLeft (β := fun j => Fin (size j))).symm.trans τ.slotEquiv
      strictMono := by
        intro j
        obtain ⟨i, rfl⟩ := e.surjective j
        intro a b hab
        let localEquiv : (Σ k : ι, Fin (size (e k))) ≃
            (Σ k : κ, Fin (size k)) :=
          e.sigmaCongrLeft (β := fun k => Fin (size k))
        have ha : localEquiv.symm ⟨e i, a⟩ = ⟨i, a⟩ := by
          apply localEquiv.injective
          simp [localEquiv]
        have hb : localEquiv.symm ⟨e i, b⟩ = ⟨i, b⟩ := by
          apply localEquiv.injective
          simp [localEquiv]
        change τ.slotEquiv (localEquiv.symm ⟨e i, a⟩) <
          τ.slotEquiv (localEquiv.symm ⟨e i, b⟩)
        rw [ha, hb]
        exact τ.strictMono i hab }
  left_inv σ := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    intro v
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  right_inv τ := by
    apply FamilySlotShuffleTo.ext
    apply Equiv.ext
    intro v
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

/-- Renaming the block-index type of both shuffles leaves their ambient
slot relabeling literally unchanged. Thus all ordered integrals are
transported by the same permutation, independently of block names. -/
theorem FamilySlotShuffleTo.reindexEquiv_ambientRelabel
    {κ : Type*} (e : ι ≃ κ) (size : κ → ℕ) {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) :
    ((FamilySlotShuffleTo.reindexEquiv e size) σ).ambientRelabel
        ((FamilySlotShuffleTo.reindexEquiv e size) τ) =
      σ.ambientRelabel τ := by
  ext v
  simp [FamilySlotShuffleTo.ambientRelabel,
    FamilySlotShuffleTo.reindexEquiv, Equiv.trans_apply]

/-- After a block renaming the inverse shuffle returns the renamed
owner at each fixed global slot. -/
theorem FamilySlotShuffleTo.reindexEquiv_owner
    {κ : Type*} (e : ι ≃ κ) (size : κ → ℕ) {total : ℕ}
    (σ : FamilySlotShuffleTo size total) (v : Fin total) :
    (((FamilySlotShuffleTo.reindexEquiv e size) σ).slotEquiv.symm v).1 =
      e.symm ((σ.slotEquiv.symm v).1) := by
  simp [FamilySlotShuffleTo.reindexEquiv, Equiv.sigmaCongrLeft,
    Equiv.trans_apply]

/-- Casting only the type-level family-size function does not alter
which block owns an ambient slot. -/
theorem FamilySlotShuffleTo.castSize_owner
    {size₁ size₂ : ι → ℕ} {total : ℕ}
    (h : size₁ = size₂) (σ : FamilySlotShuffleTo size₁ total)
    (v : Fin total) :
    (((Equiv.cast (congrArg (fun s => FamilySlotShuffleTo s total) h)) σ).slotEquiv.symm v).1 =
      (σ.slotEquiv.symm v).1 := by
  cases h
  rfl

/-- Casting only the type-level family-size function preserves the
ambient permutation between two family shuffles. -/
theorem FamilySlotShuffleTo.castSize_ambientRelabel
    {size₁ size₂ : ι → ℕ} {total : ℕ}
    (h : size₁ = size₂)
    (σ τ : FamilySlotShuffleTo size₁ total) :
    (((Equiv.cast (congrArg (fun s => FamilySlotShuffleTo s total) h)) σ).ambientRelabel
      ((Equiv.cast (congrArg (fun s => FamilySlotShuffleTo s total) h)) τ)) =
      σ.ambientRelabel τ := by
  cases h
  rfl

/-- Changing the ambient cardinality proof only casts slot numbers;
it does not modify the family owner of an ambient slot. -/
theorem FamilySlotShuffleTo.castTotalEquiv_owner
    {size : ι → ℕ} {m n : ℕ} (h : m = n)
    (σ : FamilySlotShuffleTo size m) (v : Fin n) :
    (((FamilySlotShuffleTo.castTotalEquiv h) σ).slotEquiv.symm v).1 =
      (σ.slotEquiv.symm (Fin.cast h.symm v)).1 := by
  cases h
  rfl

/-- Simultaneously casting both shuffles' ambient cardinalities
conjugates their ambient permutation by the same Fin cast. -/
theorem FamilySlotShuffleTo.castTotalEquiv_ambientRelabel
    {size : ι → ℕ} {m n : ℕ} (h : m = n)
    (σ τ : FamilySlotShuffleTo size m) :
    (((FamilySlotShuffleTo.castTotalEquiv h) σ).ambientRelabel
      ((FamilySlotShuffleTo.castTotalEquiv h) τ)) =
      ((Fin.castOrderIso h).symm.toEquiv.trans
        (σ.ambientRelabel τ)).trans (Fin.castOrderIso h).toEquiv := by
  cases h
  ext v
  simp [FamilySlotShuffleTo.ambientRelabel, FamilySlotShuffleTo.castTotalEquiv]

end Combinatorics

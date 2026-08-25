import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv
import LeanCondensedMatter.Combinatorics.SumEquivPartition
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false

/-!
# Recursive decomposition of finite-family slot shuffles

A shuffle of `k + 1` ordered slot blocks decomposes into a binary shuffle of the head block against
all tail slots, together with a shuffle internal to the tail family. This is the combinatorial
recursion needed for the finite-family ordered-simplex product identity.
-/

namespace Combinatorics

open BinaryShuffle

variable {k : ℕ}

/-- The family obtained by dropping the head block. -/
abbrev FamilySlotShuffle.tailSize (size : Fin (k + 1) → ℕ) : Fin k → ℕ :=
  fun i => size i.succ

/-- The total number of slots in the tail family. -/
abbrev FamilySlotShuffle.tailTotal (size : Fin (k + 1) → ℕ) : ℕ :=
  ∑ i : Fin k, size i.succ

/-- Split the total size into the head block and the tail family. -/
theorem FamilySlotShuffle.sum_eq_head_add_tail (size : Fin (k + 1) → ℕ) :
    (∑ i, size i) = size 0 + ∑ i : Fin k, size i.succ := by
  exact Fin.sum_univ_succ size

/-- Separate the head local-slot fiber from the sigma type of tail fibers. -/
def FamilySlotShuffle.headTailLocalSlotEquiv (size : Fin (k + 1) → ℕ) :
    (Σ i : Fin (k + 1), Fin (size i)) ≃
      Fin (size 0) ⊕ (Σ i : Fin k, Fin (size i.succ)) where
  toFun x := Fin.cases (fun j => Sum.inl j) (fun i j => Sum.inr ⟨i, j⟩) x.1 x.2
  invFun
    | Sum.inl j => ⟨0, j⟩
    | Sum.inr x => ⟨x.1.succ, x.2⟩
  left_inv := by
    rintro ⟨i, j⟩
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  right_inv := by
    rintro (j | ⟨i, j⟩) <;> rfl

@[simp]
theorem FamilySlotShuffle.headTailLocalSlotEquiv_zero (size : Fin (k + 1) → ℕ)
    (j : Fin (size 0)) :
    FamilySlotShuffle.headTailLocalSlotEquiv size ⟨0, j⟩ = Sum.inl j :=
  rfl

@[simp]
theorem FamilySlotShuffle.headTailLocalSlotEquiv_succ (size : Fin (k + 1) → ℕ)
    (i : Fin k) (j : Fin (size i.succ)) :
    FamilySlotShuffle.headTailLocalSlotEquiv size ⟨i.succ, j⟩ = Sum.inr ⟨i, j⟩ :=
  rfl

@[simp]
theorem FamilySlotShuffle.headTailLocalSlotEquiv_symm_inl (size : Fin (k + 1) → ℕ)
    (j : Fin (size 0)) :
    (FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inl j) = ⟨0, j⟩ :=
  rfl

@[simp]
theorem FamilySlotShuffle.headTailLocalSlotEquiv_symm_inr (size : Fin (k + 1) → ℕ)
    (x : Σ i : Fin k, Fin (size i.succ)) :
    (FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inr x) = ⟨x.1.succ, x.2⟩ :=
  rfl

/-- View a family shuffle as an equivalence from the head/tail sum decomposition to ambient slots. -/
def FamilySlotShuffle.headTailSlotEquiv {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) :
    Fin (size 0) ⊕ (Σ i : Fin k, Fin (size i.succ)) ≃ Fin (∑ i, size i) :=
  (FamilySlotShuffle.headTailLocalSlotEquiv size).symm.trans shuffle.slotEquiv

/-- Combine a head-versus-tail binary shuffle with an internal tail-family shuffle. -/
noncomputable def FamilySlotShuffle.cons (size : Fin (k + 1) → ℕ)
    (outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size))
    (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size)) :
    FamilySlotShuffle size where
  slotEquiv :=
    (FamilySlotShuffle.headTailLocalSlotEquiv size).trans
      ((Equiv.sumCongr (Equiv.refl _) tail.slotEquiv).trans
        (outer.slotEquiv.trans
          (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm)))
  strictMono := by
    intro i
    refine Fin.cases ?_ (fun r => ?_) i
    · intro a b hab
      change (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm)
          (outer.slotEquiv (Sum.inl a)) <
        (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm)
          (outer.slotEquiv (Sum.inl b))
      simpa using outer.strictMonoLeft hab
    · intro a b hab
      change (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm)
          (outer.slotEquiv (Sum.inr (tail.slotEquiv ⟨r, a⟩))) <
        (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm)
          (outer.slotEquiv (Sum.inr (tail.slotEquiv ⟨r, b⟩)))
      simpa using outer.strictMonoRight (tail.strictMono r hab)

@[simp]
theorem FamilySlotShuffle.cons_slotEquiv_zero (size : Fin (k + 1) → ℕ)
    (outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size))
    (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size))
    (j : Fin (size 0)) :
    (FamilySlotShuffle.cons size outer tail).slotEquiv ⟨0, j⟩ =
      finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm
        (outer.slotEquiv (Sum.inl j)) :=
  rfl

@[simp]
theorem FamilySlotShuffle.cons_slotEquiv_succ (size : Fin (k + 1) → ℕ)
    (outer : SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size))
    (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size))
    (i : Fin k) (j : Fin (size i.succ)) :
    (FamilySlotShuffle.cons size outer tail).slotEquiv ⟨i.succ, j⟩ =
      finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm
        (outer.slotEquiv (Sum.inr (tail.slotEquiv ⟨i, j⟩))) :=
  rfl

/-- Ambient slots occupied by the head block. -/
def FamilySlotShuffle.headSlots {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) : Finset (Fin (∑ i, size i)) :=
  SumEquiv.leftImage shuffle.headTailSlotEquiv

/-- Ambient slots occupied by all tail blocks. -/
def FamilySlotShuffle.tailSlots {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) : Finset (Fin (∑ i, size i)) :=
  SumEquiv.rightImage shuffle.headTailSlotEquiv

@[simp]
theorem FamilySlotShuffle.card_headSlots {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) : shuffle.headSlots.card = size 0 := by
  simpa [FamilySlotShuffle.headSlots] using
    (SumEquiv.card_leftImage shuffle.headTailSlotEquiv)

@[simp]
theorem FamilySlotShuffle.card_tailSlots {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) :
    shuffle.tailSlots.card = FamilySlotShuffle.tailTotal size := by
  simpa [FamilySlotShuffle.tailSlots, Fintype.card_sigma] using
    (SumEquiv.card_rightImage shuffle.headTailSlotEquiv)

@[simp]
theorem FamilySlotShuffle.mem_headSlots_iff {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) (x : Fin (∑ i, size i)) :
    x ∈ shuffle.headSlots ↔ ∃ j : Fin (size 0), shuffle.slotEquiv ⟨0, j⟩ = x := by
  simpa [FamilySlotShuffle.headSlots, FamilySlotShuffle.headTailSlotEquiv] using
    (SumEquiv.mem_leftImage_iff shuffle.headTailSlotEquiv x)

@[simp]
theorem FamilySlotShuffle.mem_tailSlots_iff {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) (x : Fin (∑ i, size i)) :
    x ∈ shuffle.tailSlots ↔ ∃ y : Σ i : Fin k, Fin (size i.succ),
      shuffle.slotEquiv
        ((FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inr y)) = x := by
  simpa [FamilySlotShuffle.tailSlots, FamilySlotShuffle.headTailSlotEquiv] using
    (SumEquiv.mem_rightImage_iff shuffle.headTailSlotEquiv x)

/-- The tail slots are exactly the complement of the head slots. -/
theorem FamilySlotShuffle.mem_tailSlots_iff_not_mem_headSlots
    {size : Fin (k + 1) → ℕ} (shuffle : FamilySlotShuffle size)
    (x : Fin (∑ i, size i)) :
    x ∈ shuffle.tailSlots ↔ x ∉ shuffle.headSlots := by
  simpa [FamilySlotShuffle.headSlots, FamilySlotShuffle.tailSlots] using
    (SumEquiv.mem_rightImage_iff_not_mem_leftImage shuffle.headTailSlotEquiv x)

/-- The head local slots, viewed as the subtype of ambient head slots. -/
noncomputable def FamilySlotShuffle.headSlotSubtypeEquiv
    {size : Fin (k + 1) → ℕ} (shuffle : FamilySlotShuffle size) :
    Fin (size 0) ≃ ↥shuffle.headSlots :=
  SumEquiv.leftSubtypeEquiv shuffle.headTailSlotEquiv

/-- The tail local slots, viewed as the subtype of ambient tail slots. -/
noncomputable def FamilySlotShuffle.tailSlotSubtypeEquiv
    {size : Fin (k + 1) → ℕ} (shuffle : FamilySlotShuffle size) :
    (Σ i : Fin k, Fin (size i.succ)) ≃ ↥shuffle.tailSlots :=
  SumEquiv.rightSubtypeEquiv shuffle.headTailSlotEquiv

@[simp]
theorem FamilySlotShuffle.tailSlotSubtypeEquiv_val
    {size : Fin (k + 1) → ℕ} (shuffle : FamilySlotShuffle size)
    (y : Σ i : Fin k, Fin (size i.succ)) :
    ((shuffle.tailSlotSubtypeEquiv y : ↥shuffle.tailSlots) : Fin (∑ i, size i)) =
      shuffle.slotEquiv
        ((FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inr y)) := by
  rfl

/-- The ambient tail-slot subtype is the set-theoretic complement of the ambient head-slot subtype. -/
theorem FamilySlotShuffle.tailSlots_set_eq_compl_headSlots
    {size : Fin (k + 1) → ℕ} (shuffle : FamilySlotShuffle size) :
    (↑shuffle.tailSlots : Set (Fin (∑ i, size i))) =
      (↑shuffle.headSlots : Set (Fin (∑ i, size i)))ᶜ := by
  ext x
  simp [shuffle.mem_tailSlots_iff_not_mem_headSlots x]

/-- Extract the shuffle internal to the tail family. -/
noncomputable def FamilySlotShuffle.tailShuffle {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) :
    FamilySlotShuffle (FamilySlotShuffle.tailSize size) where
  slotEquiv := shuffle.tailSlotSubtypeEquiv.trans
    (shuffle.tailSlots.orderIsoOfFin shuffle.card_tailSlots).symm.toEquiv
  strictMono := by
    intro i a b hab
    apply (shuffle.tailSlots.orderIsoOfFin shuffle.card_tailSlots).symm.strictMono
    change shuffle.slotEquiv
        ((FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inr ⟨i, a⟩)) <
      shuffle.slotEquiv
        ((FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inr ⟨i, b⟩))
    simpa using shuffle.strictMono i.succ hab

/-- The head-versus-tail ambient slot equivalence, assembled from the head subset, its complement,
and the canonical finite order on tail slots. -/
noncomputable def FamilySlotShuffle.outerSlotEquiv {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) :
    Fin (size 0) ⊕ Fin (FamilySlotShuffle.tailTotal size) ≃
      Fin (size 0 + FamilySlotShuffle.tailTotal size) :=
  (Equiv.sumCongr shuffle.headSlotSubtypeEquiv
      ((shuffle.tailSlots.orderIsoOfFin shuffle.card_tailSlots).toEquiv.trans
        (Equiv.setCongr shuffle.tailSlots_set_eq_compl_headSlots))).trans
    ((Equiv.Set.sumCompl (↑shuffle.headSlots : Set (Fin (∑ i, size i)))).trans
      (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size)))

@[simp]
theorem FamilySlotShuffle.outerSlotEquiv_apply_inl {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) (j : Fin (size 0)) :
    shuffle.outerSlotEquiv (Sum.inl j) =
      finCongr (FamilySlotShuffle.sum_eq_head_add_tail size)
        (shuffle.slotEquiv ⟨0, j⟩) := by
  rfl

@[simp]
theorem FamilySlotShuffle.outerSlotEquiv_apply_inr {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) (r : Fin (FamilySlotShuffle.tailTotal size)) :
    shuffle.outerSlotEquiv (Sum.inr r) =
      finCongr (FamilySlotShuffle.sum_eq_head_add_tail size)
        ((shuffle.tailSlots.orderIsoOfFin shuffle.card_tailSlots r :
          ↥shuffle.tailSlots) : Fin (∑ i, size i)) := by
  rfl

/-- Extract the binary shuffle of the head block against all tail slots. -/
noncomputable def FamilySlotShuffle.outerShuffle {size : Fin (k + 1) → ℕ}
    (shuffle : FamilySlotShuffle size) :
    SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size) where
  slotEquiv := shuffle.outerSlotEquiv
  strictMonoLeft := by
    intro a b hab
    change shuffle.outerSlotEquiv (Sum.inl a) < shuffle.outerSlotEquiv (Sum.inl b)
    rw [shuffle.outerSlotEquiv_apply_inl, shuffle.outerSlotEquiv_apply_inl]
    simpa using shuffle.strictMono 0 hab
  strictMonoRight := by
    intro a b hab
    change shuffle.outerSlotEquiv (Sum.inr a) < shuffle.outerSlotEquiv (Sum.inr b)
    rw [shuffle.outerSlotEquiv_apply_inr, shuffle.outerSlotEquiv_apply_inr]
    simpa using (shuffle.tailSlots.orderIsoOfFin shuffle.card_tailSlots).strictMono hab

/-- Recombining the extracted outer and tail shuffles recovers the original family shuffle. -/
theorem FamilySlotShuffle.cons_outerShuffle_tailShuffle
    {size : Fin (k + 1) → ℕ} (shuffle : FamilySlotShuffle size) :
    FamilySlotShuffle.cons size shuffle.outerShuffle shuffle.tailShuffle = shuffle := by
  apply FamilySlotShuffle.ext
  apply Equiv.ext
  rintro ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
      simp [FamilySlotShuffle.outerShuffle]
  | succ r =>
      simp [FamilySlotShuffle.tailShuffle, FamilySlotShuffle.outerShuffle]

/-- The recursive constructor is injective. -/
theorem FamilySlotShuffle.cons_injective (size : Fin (k + 1) → ℕ) :
    Function.Injective (fun p :
      SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size) ×
        FamilySlotShuffle (FamilySlotShuffle.tailSize size) =>
      FamilySlotShuffle.cons size p.1 p.2) := by
  rintro ⟨outer₁, tail₁⟩ ⟨outer₂, tail₂⟩ h
  have hleft : ∀ j : Fin (size 0),
      outer₁.slotEquiv (Sum.inl j) = outer₂.slotEquiv (Sum.inl j) := by
    intro j
    have hj := congrArg
      (fun shuffle : FamilySlotShuffle size =>
        shuffle.slotEquiv
          (⟨(0 : Fin (k + 1)), j⟩ : Σ i : Fin (k + 1), Fin (size i))) h
    exact (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm).injective hj
  have houter : outer₁ = outer₂ := by
    apply SlotShuffle.eq_of_leftSlots_eq
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (outer₁.mem_leftSlots_iff x).1 hx
      exact (outer₂.mem_leftSlots_iff x).2 ⟨j, (hleft j).symm.trans hj⟩
    · intro hx
      obtain ⟨j, hj⟩ := (outer₂.mem_leftSlots_iff x).1 hx
      exact (outer₁.mem_leftSlots_iff x).2 ⟨j, (hleft j).trans hj⟩
  subst outer₂
  have htail : tail₁ = tail₂ := by
    apply FamilySlotShuffle.ext
    apply Equiv.ext
    intro x
    have hx := congrArg
      (fun shuffle : FamilySlotShuffle size =>
        shuffle.slotEquiv
          ((FamilySlotShuffle.headTailLocalSlotEquiv size).symm (Sum.inr x))) h
    have hx' := (finCongr (FamilySlotShuffle.sum_eq_head_add_tail size).symm).injective hx
    have hx'' := outer₁.slotEquiv.injective hx'
    exact Sum.inr.inj hx''
  exact Prod.ext rfl htail

/-- Shuffles of `k + 1` blocks are equivalent to a head-versus-tail binary shuffle and a tail-family
shuffle. -/
noncomputable def FamilySlotShuffle.consEquiv (size : Fin (k + 1) → ℕ) :
    SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size) ×
        FamilySlotShuffle (FamilySlotShuffle.tailSize size) ≃
      FamilySlotShuffle size :=
  Equiv.ofBijective
    (fun p => FamilySlotShuffle.cons size p.1 p.2)
    ⟨FamilySlotShuffle.cons_injective size, by
      intro shuffle
      exact ⟨⟨shuffle.outerShuffle, shuffle.tailShuffle⟩,
        shuffle.cons_outerShuffle_tailShuffle⟩⟩

end Combinatorics

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Perm

set_option linter.style.header false

/-!
# Order-preserving shuffles of a finite family of slot blocks

`FamilySlotShuffle size` interleaves one ordered block `Fin (size i)` for every finite index `i`
into `Fin (∑ i, size i)`, preserving the order inside each block.  This is the statistics- and
diagram-independent form of a component shuffle.
-/

namespace Combinatorics

variable {ι : Type*} [Fintype ι]

/-- An order-preserving interleaving of a finite family of local slot blocks. -/
structure FamilySlotShuffle (size : ι → ℕ) where
  slotEquiv : (Σ i : ι, Fin (size i)) ≃ Fin (∑ i, size i)
  strictMono : ∀ i, StrictMono (fun j => slotEquiv ⟨i, j⟩)

@[ext]
theorem FamilySlotShuffle.ext {size : ι → ℕ} {σ τ : FamilySlotShuffle size}
    (h : σ.slotEquiv = τ.slotEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Finite-family shuffles form a finite type when the finite index type has decidable equality. -/
noncomputable instance FamilySlotShuffle.instFintype [DecidableEq ι] (size : ι → ℕ) :
    Fintype (FamilySlotShuffle size) :=
  Fintype.ofInjective (fun shuffle : FamilySlotShuffle size => shuffle.slotEquiv)
    (fun _ _ h => FamilySlotShuffle.ext h)

/-- The unique shuffle of an empty family of slot blocks. -/
noncomputable def FamilySlotShuffle.nil (size : Fin 0 → ℕ) : FamilySlotShuffle size where
  slotEquiv := Fintype.equivOfCardEq (by simp)
  strictMono := fun i => Fin.elim0 i

/-- A shuffle of an empty family is unique. -/
noncomputable instance FamilySlotShuffle.instUniqueZero (size : Fin 0 → ℕ) :
    Unique (FamilySlotShuffle size) where
  default := FamilySlotShuffle.nil size
  uniq shuffle := by
    apply FamilySlotShuffle.ext
    apply Equiv.ext
    rintro ⟨i, _⟩
    exact Fin.elim0 i

/-- Restrict an ambient time assignment to one local block. -/
def FamilySlotShuffle.timeAssignment {size : ι → ℕ} (shuffle : FamilySlotShuffle size)
    (τ : Fin (∑ i, size i) → ℝ) (i : ι) : Fin (size i) → ℝ :=
  fun j => τ (shuffle.slotEquiv ⟨i, j⟩)

@[simp]
theorem FamilySlotShuffle.timeAssignment_apply {size : ι → ℕ}
    (shuffle : FamilySlotShuffle size) (τ : Fin (∑ i, size i) → ℝ)
    (i : ι) (j : Fin (size i)) :
    shuffle.timeAssignment τ i j = τ (shuffle.slotEquiv ⟨i, j⟩) :=
  rfl

/-- Product of local integrands after all local coordinates are embedded by a family shuffle. -/
noncomputable def FamilySlotShuffle.integrand {size : ι → ℕ}
    (shuffle : FamilySlotShuffle size)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (τ : Fin (∑ i, size i) → ℝ) : ℂ :=
  ∏ i, localIntegrand i (shuffle.timeAssignment τ i)

/-- Coordinate restriction to one local block is continuous. -/
theorem FamilySlotShuffle.continuous_timeAssignment {size : ι → ℕ}
    (shuffle : FamilySlotShuffle size) (i : ι) :
    Continuous (fun τ : Fin (∑ i, size i) → ℝ => shuffle.timeAssignment τ i) := by
  exact continuous_pi fun j => continuous_apply (shuffle.slotEquiv ⟨i, j⟩)

/-- A finite product of continuous local integrands remains continuous after shuffling. -/
theorem FamilySlotShuffle.continuous_integrand {size : ι → ℕ}
    (shuffle : FamilySlotShuffle size)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    Continuous (shuffle.integrand localIntegrand) := by
  unfold FamilySlotShuffle.integrand
  exact continuous_finsetProd _ fun i _ =>
    (hlocal i).comp (shuffle.continuous_timeAssignment i)

end Combinatorics

import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Integrands associated with finite-family slot shuffles

Coordinate restriction, shuffled products, and continuity belong to the ordered-simplex analysis
layer.  The underlying `FamilySlotShuffle` remains pure finite combinatorics.
-/

namespace Combinatorics

variable {ι : Type*} [Fintype ι]

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

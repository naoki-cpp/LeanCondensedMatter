import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import LeanCondensedMatter.Combinatorics.FamilySlotShuffleDecomposition
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Integrands associated with finite-family slot shuffles

Coordinate restriction, shuffled products, continuity, and measurable local boundedness belong to the
ordered-simplex analysis layer. The canonical integrand API is defined on `FamilySlotShuffleTo`,
with `FamilySlotShuffle` using it directly as the canonical-total abbreviation.
-/

namespace Combinatorics

variable {ι : Type*}

/-- Restrict an ambient assignment to one local block for a shuffle into an arbitrary ambient total. -/
def FamilySlotShuffleTo.timeAssignment {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (τ : Fin total → ℝ) (i : ι) :
    Fin (size i) → ℝ :=
  fun j => τ (shuffle.slotEquiv ⟨i, j⟩)

@[simp]
theorem FamilySlotShuffleTo.timeAssignment_apply {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (τ : Fin total → ℝ)
    (i : ι) (j : Fin (size i)) :
    shuffle.timeAssignment τ i j = τ (shuffle.slotEquiv ⟨i, j⟩) :=
  rfl

variable [Fintype ι]

/-- Product of local integrands after embedding their coordinates into an arbitrary ambient total.
This is the `FamilySlotShuffleTo` form used when the ambient cardinality is only propositionally
equal to the sum of local block sizes. -/
noncomputable def FamilySlotShuffleTo.ambientIntegrand {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (τ : Fin total → ℝ) : ℂ :=
  ∏ i, localIntegrand i (shuffle.timeAssignment τ i)

/-- The integrand of a family shuffle assembled from an outer head/tail shuffle is the binary
integrand of the head block and its shuffled tail. -/
theorem FamilySlotShuffle.cons_integrand {k : ℕ}
    (size : Fin (k + 1) → ℕ)
    (outer : BinaryShuffle.SlotShuffle (size 0) (FamilySlotShuffle.tailTotal size))
    (tail : FamilySlotShuffle (FamilySlotShuffle.tailSize size))
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (τ : Fin (size 0 + FamilySlotShuffle.tailTotal size) → ℝ) :
    (FamilySlotShuffle.cons size outer tail).ambientIntegrand localIntegrand
        (fun j => τ (Fin.cast (Fin.sum_univ_succ size) j)) =
      outer.integrand (localIntegrand 0)
        (tail.ambientIntegrand (fun i => localIntegrand i.succ)) τ := by
  unfold FamilySlotShuffleTo.ambientIntegrand BinaryShuffle.SlotShuffle.integrand
  rw [Fin.prod_univ_succ]
  apply congrArg₂ (· * ·)
  · apply congrArg (localIntegrand 0)
    funext j
    simp [FamilySlotShuffleTo.timeAssignment]
  · apply congrArg (fun h : Fin k → ℂ => ∏ i, h i)
    funext i
    apply congrArg (localIntegrand i.succ)
    funext j
    simp [FamilySlotShuffleTo.timeAssignment]

/-- Coordinate restriction to one local block is continuous. -/
omit [Fintype ι] in
private theorem FamilySlotShuffleTo.continuous_timeAssignment {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (i : ι) :
    Continuous (fun τ : Fin total → ℝ => shuffle.timeAssignment τ i) := by
  exact continuous_pi fun j => continuous_apply (shuffle.slotEquiv ⟨i, j⟩)

/-- A finite product of continuous local integrands remains continuous after embedding their
coordinates by an arbitrary-total family shuffle. -/
theorem FamilySlotShuffleTo.continuous_ambientIntegrand {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    Continuous (shuffle.ambientIntegrand localIntegrand) := by
  unfold FamilySlotShuffleTo.ambientIntegrand
  exact continuous_finsetProd _ fun i _ =>
    (hlocal i).comp (shuffle.continuous_timeAssignment i)

/-- A finite product of measurable locally bounded local integrands remains measurable locally
bounded after embedding their coordinates by an arbitrary-total family shuffle. -/
theorem FamilySlotShuffleTo.measurableLocallyBounded_ambientIntegrand
    {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, intervalIntegral.MeasurableLocallyBounded (localIntegrand i)) :
    intervalIntegral.MeasurableLocallyBounded (shuffle.ambientIntegrand localIntegrand) := by
  classical
  change intervalIntegral.MeasurableLocallyBounded
    (fun τ : Fin total → ℝ =>
      ∏ i, localIntegrand i (fun j => τ (shuffle.slotEquiv ⟨i, j⟩)))
  simpa using
    intervalIntegral.MeasurableLocallyBounded.finsetProd Finset.univ
      (fun i τ => localIntegrand i (fun j => τ (shuffle.slotEquiv ⟨i, j⟩)))
      (fun i _ => (hlocal i).comp_finCoordinateSelection
        (fun j => shuffle.slotEquiv ⟨i, j⟩))

end Combinatorics

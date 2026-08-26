import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Integrands associated with finite-family slot shuffles

Coordinate restriction, shuffled products, continuity, and measurable local boundedness belong to the
ordered-simplex analysis layer. The underlying `FamilySlotShuffle` remains pure finite combinatorics.
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

/-- Product of local integrands after all local coordinates are embedded by a family shuffle. -/
noncomputable def FamilySlotShuffle.integrand {size : ι → ℕ}
    (shuffle : FamilySlotShuffle size)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (τ : Fin (∑ i, size i) → ℝ) : ℂ :=
  ∏ i, localIntegrand i (shuffle.timeAssignment τ i)

/-- Coordinate restriction to one local block is continuous. -/
private theorem FamilySlotShuffle.continuous_timeAssignment {size : ι → ℕ}
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

/-- A finite product of measurable locally bounded local integrands remains measurable locally
bounded after a family shuffle. -/
theorem FamilySlotShuffle.measurableLocallyBounded_integrand {size : ι → ℕ}
    (shuffle : FamilySlotShuffle size)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, intervalIntegral.MeasurableLocallyBounded (localIntegrand i)) :
    intervalIntegral.MeasurableLocallyBounded (shuffle.integrand localIntegrand) := by
  classical
  have hMeas : Measurable (shuffle.integrand localIntegrand) := by
    unfold FamilySlotShuffle.integrand
    exact Finset.measurable_prod _ fun i _ =>
      (hlocal i).1.comp (shuffle.continuous_timeAssignment i).measurable
  refine ⟨hMeas, ?_⟩
  intro R hR
  choose C hC0 hC using fun i => (hlocal i).2 R hR
  refine ⟨∏ i, C i, Finset.prod_nonneg fun i _ => hC0 i, ?_⟩
  intro τ hτ
  have hmem (i : ι) : shuffle.timeAssignment τ i ∈
      intervalIntegral.orderedSimplexTimeCube (size i) R := by
    rw [intervalIntegral.orderedSimplexTimeCube, Set.mem_Icc] at hτ ⊢
    exact ⟨fun j => hτ.1 (shuffle.slotEquiv ⟨i, j⟩),
      fun j => hτ.2 (shuffle.slotEquiv ⟨i, j⟩)⟩
  rw [FamilySlotShuffle.integrand, norm_prod]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
    (fun i _ => hC i _ (hmem i))

end Combinatorics

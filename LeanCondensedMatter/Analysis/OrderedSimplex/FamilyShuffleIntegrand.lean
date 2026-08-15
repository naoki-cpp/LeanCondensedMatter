import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Integrands associated with finite-family slot shuffles

Coordinate restriction, reconstruction, localization, shuffled products, continuity, and measurable
local boundedness belong to the ordered-simplex analysis layer. The underlying `FamilySlotShuffle`
remains pure finite combinatorics.
-/

namespace Combinatorics

namespace DependentSlotEquiv

variable {ι κ : Type*} {slot : ι → Type*}

/-- Restrict an ambient assignment along one fiber of a dependent slot equivalence. -/
def assignment (e : (Σ i, slot i) ≃ κ) (τ : κ → ℝ) (i : ι) : slot i → ℝ :=
  fun j => τ (e ⟨i, j⟩)

/-- Assemble an ambient assignment from one assignment on every dependent slot fiber. -/
def ofAssignments (e : (Σ i, slot i) ≃ κ)
    (fiberAssignment : ∀ i, slot i → ℝ) : κ → ℝ :=
  fun k =>
    let x := e.symm k
    fiberAssignment x.1 x.2

@[simp]
theorem assignment_ofAssignments (e : (Σ i, slot i) ≃ κ)
    (fiberAssignment : ∀ i, slot i → ℝ) (i : ι) :
    assignment e (ofAssignments e fiberAssignment) i = fiberAssignment i := by
  funext j
  change fiberAssignment (e.symm (e ⟨i, j⟩)).1
      (e.symm (e ⟨i, j⟩)).2 = fiberAssignment i j
  exact congrArg (fun x : Σ i, slot i => fiberAssignment x.1 x.2)
    (e.symm_apply_apply ⟨i, j⟩)

@[simp]
theorem ofAssignments_assignment (e : (Σ i, slot i) ≃ κ) (τ : κ → ℝ) :
    ofAssignments e (fun i => assignment e τ i) = τ := by
  funext k
  change τ (e (e.symm k)) = τ k
  rw [e.apply_symm_apply]

/-- Extend one fiber assignment to the ambient coordinates, using zero on every other fiber. -/
noncomputable def ofAssignment (e : (Σ i, slot i) ≃ κ) (i : ι)
    (fiberAssignment : slot i → ℝ) : κ → ℝ := by
  classical
  exact ofAssignments e (Function.update (fun _ => 0) i fiberAssignment)

@[simp]
theorem assignment_ofAssignment_self (e : (Σ i, slot i) ≃ κ) (i : ι)
    (fiberAssignment : slot i → ℝ) :
    assignment e (ofAssignment e i fiberAssignment) i = fiberAssignment := by
  classical
  simp [ofAssignment]

/-- Embedding one dependent-slot fiber into the ambient assignment space is continuous. -/
theorem continuous_ofAssignment (e : (Σ i, slot i) ≃ κ) (i : ι) :
    Continuous (ofAssignment e i) := by
  classical
  apply continuous_pi
  intro k
  rcases h : e.symm k with ⟨i', j⟩
  change Continuous (fun τ : slot i → ℝ =>
    (Function.update (fun i : ι => (0 : slot i → ℝ)) i τ
      (e.symm k).1) (e.symm k).2)
  rw [h]
  by_cases hi : i' = i
  · subst i'
    simpa using (continuous_apply j : Continuous (fun τ : slot i → ℝ => τ j))
  · simpa [hi] using
      (continuous_const : Continuous (fun _ : slot i → ℝ => (0 : ℝ)))

/-- An ambient scalar function is local to fiber `i` when it depends only on that restriction. -/
def Local (e : (Σ i, slot i) ≃ κ) (i : ι) (F : (κ → ℝ) → ℂ) : Prop :=
  ∀ τ υ, assignment e τ i = assignment e υ i → F τ = F υ

/-- Turn an ambient scalar function into a local function on one dependent slot fiber. -/
noncomputable def localize (e : (Σ i, slot i) ≃ κ) (i : ι)
    (F : (κ → ℝ) → ℂ) : (slot i → ℝ) → ℂ :=
  fun fiberAssignment => F (ofAssignment e i fiberAssignment)

/-- Recover a fiber-local ambient function from its localized form. -/
theorem eq_localize (e : (Σ i, slot i) ≃ κ) (i : ι)
    (F : (κ → ℝ) → ℂ) (hF : Local e i F) (τ : κ → ℝ) :
    F τ = localize e i F (assignment e τ i) := by
  change F τ = F (ofAssignment e i (assignment e τ i))
  apply hF
  symm
  exact assignment_ofAssignment_self e i (assignment e τ i)

end DependentSlotEquiv

variable {ι : Type*} [Fintype ι]

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

/-- Coordinate restriction to one local block is continuous for an arbitrary ambient total. -/
theorem FamilySlotShuffleTo.continuous_timeAssignment {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total) (i : ι) :
    Continuous (fun τ : Fin total → ℝ => shuffle.timeAssignment τ i) := by
  exact continuous_pi fun j => continuous_apply (shuffle.slotEquiv ⟨i, j⟩)

/-- Product of local integrands after embedding their coordinates into an arbitrary ambient total.
This is the `FamilySlotShuffleTo` form used when the ambient cardinality is only propositionally
equal to the sum of local block sizes. -/
noncomputable def FamilySlotShuffleTo.ambientIntegrand {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (τ : Fin total → ℝ) : ℂ :=
  ∏ i, localIntegrand i (shuffle.timeAssignment τ i)

/-- A finite product of continuous local integrands remains continuous after shuffling into an
arbitrary ambient total. -/
theorem FamilySlotShuffleTo.continuous_ambientIntegrand {size : ι → ℕ} {total : ℕ}
    (shuffle : FamilySlotShuffleTo size total)
    (localIntegrand : ∀ i, (Fin (size i) → ℝ) → ℂ)
    (hlocal : ∀ i, Continuous (localIntegrand i)) :
    Continuous (shuffle.ambientIntegrand localIntegrand) := by
  unfold FamilySlotShuffleTo.ambientIntegrand
  exact continuous_finsetProd _ fun i _ =>
    (hlocal i).comp (shuffle.continuous_timeAssignment i)

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

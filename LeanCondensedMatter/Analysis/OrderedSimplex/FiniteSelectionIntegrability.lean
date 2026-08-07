import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.Compact

set_option linter.style.header false

/-!
# Integrability of finite continuous selections on ordered-simplex boxes

The recursive ordered-simplex integral only ever samples finitely many time coordinates on bounded
intervals.  This file packages the compact coordinate box and a small generic analytic lemma: a
measurable function that, pointwise on a compact set, agrees with one member of a finite family of
continuous functions is bounded and hence integrable there.

This is deliberately weaker than continuity of the selected function.  The branch choice may jump
across measurable walls; only finiteness of the branch family and continuity of each fixed branch are
used for the bound.
-/

namespace intervalIntegral

open MeasureTheory

/-- The unordered compact coordinate box containing every order-`n` recursively oriented
ordered-simplex time assignment with outer bound `β`. -/
def orderedSimplexTimeBox (n : ℕ) (β : ℝ) : Set (Fin n → ℝ) :=
  {τ | ∀ i, τ i ∈ Set.uIcc (0 : ℝ) β}

/-- The ordered-simplex coordinate box is compact. -/
theorem isCompact_orderedSimplexTimeBox (n : ℕ) (β : ℝ) :
    IsCompact (orderedSimplexTimeBox n β) := by
  simpa [orderedSimplexTimeBox] using
    (isCompact_pi_infinite (s := fun _ : Fin n => Set.uIcc (0 : ℝ) β)
      (fun _ => isCompact_uIcc))

/-- The ordered-simplex coordinate box is Borel measurable. -/
theorem measurableSet_orderedSimplexTimeBox (n : ℕ) (β : ℝ) :
    MeasurableSet (orderedSimplexTimeBox n β) :=
  (isCompact_orderedSimplexTimeBox n β).isClosed.measurableSet

/-- A pointwise selection from finitely many continuous branches is uniformly norm-bounded on a
compact set.  No regularity of the branch selector itself is required. -/
theorem exists_norm_bound_on_compact_of_finite_continuous_selection
    {ι X E : Type*} [Fintype ι] [TopologicalSpace X] [SeminormedAddGroup E]
    (K : Set X) (hK : IsCompact K) (f : X → E) (g : ι → X → E)
    (hg : ∀ i, Continuous (g i))
    (hselect : ∀ x ∈ K, ∃ i, f x = g i x) :
    ∃ C : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C := by
  classical
  let envelope : X → ℝ := fun x => ∑ i : ι, ‖g i x‖
  have hEnvelope : Continuous envelope := by
    dsimp [envelope]
    exact continuous_finsetSum _ fun i _ => (hg i).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hEnvelope.continuousOn
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hselect x hx
  have hterm : ‖f x‖ ≤ envelope x := by
    rw [hi]
    dsimp [envelope]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (g j x)) (Finset.mem_univ i)
  have hnonneg : 0 ≤ envelope x := by
    dsimp [envelope]
    exact Finset.sum_nonneg fun j _ => norm_nonneg (g j x)
  have hbound := hC x hx
  have hEnvelopeLe : envelope x ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound
  exact hterm.trans hEnvelopeLe

/-- A measurable pointwise selection from finitely many continuous branches is integrable on an
ordered-simplex coordinate box. -/
theorem integrableOn_orderedSimplexTimeBox_of_finite_continuous_selection
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → E) (g : ι → (Fin n → ℝ) → E)
    (hf : Measurable f) (hg : ∀ i, Continuous (g i))
    (hselect : ∀ x ∈ orderedSimplexTimeBox n β, ∃ i, f x = g i x) :
    IntegrableOn f (orderedSimplexTimeBox n β) := by
  obtain ⟨C, hC⟩ :=
    exists_norm_bound_on_compact_of_finite_continuous_selection
      (orderedSimplexTimeBox n β) (isCompact_orderedSimplexTimeBox n β) f g hg hselect
  apply MeasureTheory.integrableOn_of_bounded
  · exact (isCompact_orderedSimplexTimeBox n β).measure_ne_top
  · exact hf.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_orderedSimplexTimeBox n β)] with x hx
    exact hC x hx

end intervalIntegral

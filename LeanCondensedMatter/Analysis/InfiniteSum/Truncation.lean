import Mathlib.Analysis.Normed.Group.Tannery

set_option linter.style.header false

/-!
# Convergence under coordinate masks

For an absolutely summable family, pointwise eventually exhaustive coordinate masks preserve
the limit of its infinite sum. This works along an arbitrary filter, without countability,
monotonicity, or finite-rank hypotheses on the masks.
-/

open Filter Topology

noncomputable section

/-- An absolutely summable series is the limit of its masked sums whenever each index is
eventually retained. The masks need not be monotone or have finite support. -/
theorem tendsto_tsum_ite_of_eventually
    {ι κ E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ι → E) (hf : Summable (fun i => ‖f i‖))
    (l : Filter κ) (P : κ → ι → Prop) [DecidableRel P]
    (hP : ∀ i, ∀ᶠ s in l, P s i) :
    Tendsto (fun s => ∑' i, if P s i then f i else 0) l (𝓝 (∑' i, f i)) := by
  have hpoint (i : ι) :
      Tendsto (fun s => if P s i then f i else 0) l (𝓝 (f i)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hP i] with s hs
    simp [hs]
  have hbound :
      ∀ᶠ s in l, ∀ i : ι, ‖if P s i then f i else 0‖ ≤ ‖f i‖ := by
    filter_upwards [] with s
    intro i
    by_cases h : P s i <;> simp [h]
  exact tendsto_tsum_of_dominated_convergence hf hpoint hbound

end

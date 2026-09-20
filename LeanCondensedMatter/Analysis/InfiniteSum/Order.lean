import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option linter.style.header false

/-!
# Order properties of infinite sums

Generic order lemmas for summable real families.
-/

/-- If two summable real families are pointwise ordered and have the same total sum, then they are
equal term by term. -/
theorem pointwise_eq_of_tsum_eq_of_le {ι : Type*} {f g : ι → ℝ}
    (hfg : ∀ i, f i ≤ g i) (hf : Summable f) (hg : Summable g)
    (hsum : ∑' i, f i = ∑' i, g i) :
    ∀ i, f i = g i := by
  intro i
  apply le_antisymm (hfg i)
  by_contra hnot
  have hlt : f i < g i := lt_of_not_ge hnot
  have hsumlt := Summable.tsum_lt_tsum hfg hlt hf hg
  exact (ne_of_lt hsumlt) hsum

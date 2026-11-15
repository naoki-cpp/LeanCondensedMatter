module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

set_option linter.style.header false

/-!
# Order properties of infinite sums

Generic order lemmas for summable real families.
-/

/-- Restricting a nonnegative summable family along an injection is strictly sum-decreasing when
one omitted term is strictly positive. -/
theorem Summable.tsum_comp_injective_lt_of_exists_not_mem
    {ι κ : Type*} {f : κ → ℝ} (hf : Summable f)
    (hf_nonneg : ∀ k, 0 ≤ f k) (e : ι → κ) (he : Function.Injective e)
    {j : κ} (hj : j ∉ Set.range e) (hjpos : 0 < f j) :
    ∑' i, f (e i) < ∑' k, f k := by
  classical
  have hsub : Summable (fun k : ↥((Set.range e)ᶜ) => f (k : κ)) :=
    hf.comp_injective Subtype.val_injective
  have hpos : 0 < ∑' k : ↥((Set.range e)ᶜ), f (k : κ) :=
    hsub.tsum_pos (fun k => hf_nonneg k) ⟨j, hj⟩ hjpos
  have hrange :
      (∑' i, f (e i)) = ∑' k : Set.range e, f (k : κ) := by
    simpa using
      (Equiv.tsum_eq (Equiv.ofInjective e he) (fun k : Set.range e => f (k : κ)))
  rw [hrange]
  linarith [hf.tsum_subtype_add_tsum_subtype_compl (Set.range e)]


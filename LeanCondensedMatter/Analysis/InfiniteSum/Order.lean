import Mathlib.Topology.Algebra.InfiniteSum.Real

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
  let e' : ι ⊕ Unit → κ := Sum.elim e (fun _ => j)
  have he' : Function.Injective e' := by
    intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl i' =>
            apply congrArg Sum.inl
            apply he
            change e i = e i' at hab
            exact hab
        | inr u =>
            exfalso
            apply hj
            refine ⟨i, ?_⟩
            change e i = j at hab
            exact hab
    | inr u =>
        cases b with
        | inl i =>
            exfalso
            apply hj
            refine ⟨i, ?_⟩
            change j = e i at hab
            exact hab.symm
        | inr u' =>
            exact congrArg Sum.inr (Subsingleton.elim u u')
  have haug : Summable (fun q : ι ⊕ Unit => f (e' q)) :=
    hf.comp_injective he'
  have hleft : Summable ((fun q : ι ⊕ Unit => f (e' q)) ∘ Sum.inl) :=
    haug.comp_injective Sum.inl_injective
  have hright : Summable ((fun q : ι ⊕ Unit => f (e' q)) ∘ Sum.inr) :=
    haug.comp_injective Sum.inr_injective
  have hsplit :
      (∑' q : ι ⊕ Unit, f (e' q)) = (∑' i, f (e i)) + f j := by
    simpa [Function.comp_def, e'] using hleft.tsum_sum hright
  have hle : ∑' q : ι ⊕ Unit, f (e' q) ≤ ∑' k, f k :=
    hasSum_le_inj e' he' (fun k _ => hf_nonneg k) (fun _ => le_rfl)
      haug.hasSum hf.hasSum
  rw [hsplit] at hle
  linarith

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

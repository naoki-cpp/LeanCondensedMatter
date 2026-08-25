import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops

set_option linter.style.header false

/-!
# Equality cases for spectral-trace bounds

This file isolates the strictness mechanism behind restricting a nonnegative summable family along
an injection. It then applies that mechanism to the diagonal trace bound for positive operators.
-/

/-- Restricting a nonnegative summable family along an injection is strictly trace-decreasing when
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

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If a positive operator has strictly positive diagonal value on every unit vector, an
orthonormal family can saturate its spectral trace only when its span has trivial orthogonal
complement. -/
theorem orthogonal_span_eq_bot_of_sum_diagonalExpectationValue_eq_spectralTrace
    {T : H →L[ℂ] H} (hT : IsCompactOperator T) (hTpos : T.IsPositive)
    (h : HasSummableRealEigenvalues T)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d)
    (hdiag_pos : ∀ v : H, ‖v‖ = 1 →
      0 < diagonalExpectationValue T hTpos.isSelfAdjoint v)
    (heq : ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) =
      spectralTrace T) :
    (Submodule.span ℂ (Set.range d))ᗮ = ⊥ := by
  classical
  obtain ⟨w, b, hsub, hb_eq⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  set g : w → ℝ := fun j =>
    diagonalExpectationValue T hTpos.isSelfAdjoint (b j) with hg_def
  have htr : HasSum g (spectralTrace T) :=
    hasSum_diagonalExpectationValue_eq_spectralTrace hT hTpos.isSelfAdjoint h b
  have hgnonneg : ∀ j : w, 0 ≤ g j := fun j => by
    simpa [g] using diagonalExpectationValue_nonneg T hTpos (b j)
  have hd_inj : Function.Injective d := hd.linearIndependent.injective
  set e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩ with he_def
  have he_inj : Function.Injective e := fun i j hij =>
    hd_inj (congrArg Subtype.val hij)
  have hge : ∀ i, g (e i) =
      diagonalExpectationValue T hTpos.isSelfAdjoint (d i) := fun i => by
    change diagonalExpectationValue T hTpos.isSelfAdjoint (b (e i)) = _
    rw [show (b (e i) : H) = d i from by rw [hb_eq]]
  have heqg : ∑' i, g (e i) = spectralTrace T := by
    calc
      ∑' i, g (e i) =
          ∑' i, diagonalExpectationValue T hTpos.isSelfAdjoint (d i) :=
        tsum_congr hge
      _ = spectralTrace T := heq
  have he_surj : Function.Surjective e := by
    by_contra hsurj
    have hsurj' : ∃ j, ∀ i, e i ≠ j := by
      simpa only [Function.Surjective, not_forall, not_exists] using hsurj
    obtain ⟨j, hj⟩ := hsurj'
    have hjrange : j ∉ Set.range e := by
      rintro ⟨i, hi⟩
      exact hj i hi
    have hgjpos : 0 < g j := by
      simpa [g] using hdiag_pos (b j) (b.orthonormal.1 j)
    have hlt := htr.summable.tsum_comp_injective_lt_of_exists_not_mem
      hgnonneg e he_inj hjrange hgjpos
    have hlt_trace : ∑' i, g (e i) < spectralTrace T := by
      rwa [htr.tsum_eq] at hlt
    exact (ne_of_lt hlt_trace) heqg
  apply le_antisymm
  · intro x hx
    have hinner : ∀ j : w, inner ℂ (b j) x = 0 := by
      intro j
      obtain ⟨i, hi⟩ := he_surj j
      have hbdi : b j = d i := by
        rw [← hi]
        rw [hb_eq]
      rw [hbdi]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self i)) hx
    have hrepr : b.repr x = 0 := by
      ext j
      rw [b.repr_apply_apply]
      exact hinner j
    have hx0 : x = 0 := b.repr.injective (by simpa using hrepr)
    rw [hx0]
    exact Submodule.zero_mem _
  · exact bot_le

end ContinuousLinearMap

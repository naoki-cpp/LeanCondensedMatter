import LeanCondensedMatter.Analysis.InfiniteSum.Order
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops

set_option linter.style.header false

/-!
# Equality cases for spectral-trace bounds

This file applies generic infinite-sum strictness results to equality cases for the diagonal trace
bound of positive operators.
-/

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

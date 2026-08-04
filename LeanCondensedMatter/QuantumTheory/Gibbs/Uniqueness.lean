import LeanCondensedMatter.QuantumTheory.Gibbs.Equality
import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubovEquality

/-!
# Uniqueness in the Gibbs variational principle

This file reverses the inequality chain in the Gibbs–Klein proof.  The first lemmas isolate two
reusable equality mechanisms: equality of summable pointwise bounds, and equality in the combined
scalar Gibbs/logarithm estimate.
-/

/-- If two summable real families satisfy a pointwise inequality and have equal total sums, then
they agree pointwise. -/
theorem Summable.eq_of_le_of_tsum_eq
    {ι : Type*} {f g : ι → ℝ} (hf : Summable f) (hg : Summable g)
    (hfg : ∀ i, f i ≤ g i) (hsum : ∑' i, f i = ∑' i, g i) :
    ∀ i, f i = g i := by
  intro i
  apply le_antisymm (hfg i)
  by_contra hnot
  have hlt : f i < g i := lt_of_not_ge hnot
  have hsumlt := Summable.tsum_lt_tsum hfg hlt hf hg
  exact (ne_of_lt hsumlt) hsum

/-- Equality in the scalar estimate used by the Gibbs–Klein proof forces both constituent
inequalities to be equalities: the probability equals the normalized Gibbs diagonal weight, and
the logarithmic bound is saturated. -/
theorem negMulLog_bound_eq_iff {p q Z u : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hZ : 0 < Z) (hlog : -Real.log q ≤ u) :
    Real.negMulLog p = p * u + p * Real.log Z - p + q / Z ↔
      p = q / Z ∧ -Real.log q = u := by
  have hqZpos : 0 < q / Z := div_pos hq hZ
  have hgibbs := gibbs_scalar_ineq p (q / Z) hp.le hqZpos
  have hlogdiv : Real.log (q / Z) = Real.log q - Real.log Z :=
    Real.log_div hq.ne' hZ.ne'
  have hAB :
      Real.negMulLog p ≤ -p * Real.log q + p * Real.log Z - p + q / Z := by
    nlinarith [hgibbs, hlogdiv]
  have hmul : -p * Real.log q ≤ p * u := by
    have := mul_le_mul_of_nonneg_left hlog hp.le
    nlinarith
  have hBC :
      -p * Real.log q + p * Real.log Z - p + q / Z ≤
        p * u + p * Real.log Z - p + q / Z := by
    linarith
  constructor
  · intro hAC
    have hABeq :
        Real.negMulLog p = -p * Real.log q + p * Real.log Z - p + q / Z := by
      apply le_antisymm hAB
      rw [hAC]
      exact hBC
    have hBCeq :
        -p * Real.log q + p * Real.log Z - p + q / Z =
          p * u + p * Real.log Z - p + q / Z := by
      apply le_antisymm hBC
      rw [← hAC]
      exact hAB
    have hscalar :
        Real.negMulLog p + p - q / Z = -p * Real.log (q / Z) := by
      rw [hlogdiv]
      nlinarith
    have hpq := (gibbs_scalar_ineq_eq_iff p (q / Z) hp.le hqZpos).mp hscalar
    have hlogeq : -Real.log q = u := by
      nlinarith [hBCeq, hp]
    exact ⟨hpq, hlogeq⟩
  · rintro ⟨hpq, hlogeq⟩
    have hscalar :=
      (gibbs_scalar_ineq_eq_iff p (q / Z) hp.le hqZpos).mpr hpq
    rw [hlogdiv] at hscalar
    nlinarith

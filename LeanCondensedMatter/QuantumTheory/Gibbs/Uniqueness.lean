import LeanCondensedMatter.QuantumTheory.Gibbs.Equality
import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubovEquality

/-!
# Uniqueness in the Gibbs variational principle

This file reverses the inequality chain in the Gibbs–Klein proof. The scalar lemma isolates the
combined equality case needed to recover the Gibbs weights and saturated Peierls–Bogoliubov bound.
-/

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

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For nonzero inverse temperature, equality in the Helmholtz bound forces the three equality
components needed for uniqueness: the Gibbs diagonal sum saturates the trace, every density
eigenvalue equals the normalized Gibbs diagonal weight, and every Peierls–Bogoliubov bound is
saturated. -/
theorem helmholtzFreeEnergy_eq_components
    (ρ : DensityOperator H) (Hop : Observable H) (β : ℝ) (hβ : β ≠ 0)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0)
    (hfree : energyExpValue ρ Hop -
        (1 / β) * (vonNeumannEntropy ρ).toReal =
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β))) :
    (∑' a : EigenvectorIndex ρ.op,
        diagonalExpectationValue (gibbsOp Hop β)
          (gibbsOp_isPositive Hop β).isSelfAdjoint
          (eigenvectorFamily ρ.spectralTraceClass.compact a)) =
        spectralTrace (gibbsOp Hop β) ∧
      (∀ a : EigenvectorIndex ρ.op,
        a.1.1 =
          diagonalExpectationValue (gibbsOp Hop β)
            (gibbsOp_isPositive Hop β).isSelfAdjoint
            (eigenvectorFamily ρ.spectralTraceClass.compact a) /
              spectralTrace (gibbsOp Hop β)) ∧
      (∀ a : EigenvectorIndex ρ.op,
        Real.exp (-β * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a)) =
          diagonalExpectationValue (gibbsOp Hop β)
            (gibbsOp_isPositive Hop β).isSelfAdjoint
            (eigenvectorFamily ρ.spectralTraceClass.compact a)) := by
  let hsummable : HasSummableRealEigenvalues (gibbsOp Hop β) :=
    gibbsOp_hasSummableRealEigenvalues_of_isCompact Hop β hcompact
  set d := eigenvectorFamily ρ.spectralTraceClass.compact with hd_def
  set p : EigenvectorIndex ρ.op → ℝ := fun a => a.1.1 with hp_def
  set h : EigenvectorIndex ρ.op → ℝ :=
    fun a => diagonalExpectationValue Hop.1 Hop.2 (d a) with hh_def
  set q : EigenvectorIndex ρ.op → ℝ := fun a =>
    diagonalExpectationValue (gibbsOp Hop β)
      (gibbsOp_isPositive Hop β).isSelfAdjoint (d a) with hq_def
  set Z : ℝ := spectralTrace (gibbsOp Hop β) with hZ_def
  have hZpos : 0 < Z := spectralTrace_gibbsOp_pos Hop β hZ
  have hd_orth : Orthonormal ℂ d :=
    orthonormal_eigenvectorFamily ρ.spectralTraceClass.compact ρ.isSymmetric
  have hd_unit : ∀ a, ‖d a‖ = 1 := eigenvectorFamily_norm_eq_one ρ
  let hGibbs : SpectralTraceClass (gibbsOp Hop β) :=
    SpectralTraceClass.ofPositive hcompact (gibbsOp_isPositive Hop β) hsummable
  have hstep1 : ∀ a, Real.exp (-β * h a) ≤ q a := fun a => by
    simpa [hh_def, hq_def] using
      exp_neg_beta_energy_le_gibbs_diagonal Hop β (d a) (hd_unit a)
  have hqpos : ∀ a, 0 < q a := fun a => (Real.exp_pos _).trans_le (hstep1 a)
  have hstep2 : ∀ a, -Real.log (q a) ≤ β * h a := fun a =>
    neg_log_le_of_exp_le (u := β * h a) (by rw [← neg_mul]; exact hstep1 a)
  have hbound : ∀ a, Real.negMulLog (p a) ≤
      β * (p a * h a) + p a * Real.log Z - p a + q a / Z := by
    intro a
    have hb := negMulLog_le_of_neg_log_le (p := p a) (q := q a) (Z := Z)
      (u := β * h a) (ρ.eigenvalue_nonneg a) (hqpos a) hZpos (hstep2 a)
    nlinarith [hb]
  have hp_summable : Summable p :=
    ρ.spectralTraceClass.summable.congr (fun a => abs_of_nonneg (ρ.eigenvalue_nonneg a))
  obtain ⟨hph_summable, hphsum⟩ := summable_eigenvalue_mul_energy_and_tsum ρ Hop
  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z := by
    have hbound := hGibbs.sum_diagonalExpectationValue_le_trace
      (gibbsOp_isPositive Hop β).toLinearMap hd_orth
    rw [hGibbs.trace_eq_spectralTrace] at hbound
    simpa [Z, hq_def] using hbound
  have hqZ_summable : Summable (fun a => q a / Z) :=
    hq_summable_and_le.1.div_const Z
  have hplogZ_summable : Summable (fun a => p a * Real.log Z) :=
    hp_summable.mul_right _
  have hB_summable : Summable
      (fun a => β * (p a * h a) + p a * Real.log Z - p a + q a / Z) :=
    ((hph_summable.mul_left β).add hplogZ_summable).sub hp_summable |>.add hqZ_summable
  have hnegMulLog_nonneg : ∀ a, 0 ≤ Real.negMulLog (p a) :=
    fun a => Real.negMulLog_nonneg (ρ.eigenvalue_nonneg a) (ρ.eigenvalue_le_one a)
  obtain ⟨hnML_summable, hsum_le⟩ :=
    summable_and_tsum_le_of_nonneg_of_le hnegMulLog_nonneg hbound hB_summable
  obtain ⟨-, hToReal⟩ :=
    vonNeumannEntropy_ne_top_and_toReal_eq_tsum ρ hnML_summable
  have hsum_eq :
      ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) =
        β * (∑' a, p a * h a) + Real.log Z * (∑' a, p a) -
          (∑' a, p a) + ∑' a, q a / Z := by
    rw [(((hph_summable.mul_left β).add hplogZ_summable).sub hp_summable).tsum_add
      hqZ_summable, ((hph_summable.mul_left β).add hplogZ_summable).tsum_sub hp_summable,
      (hph_summable.mul_left β).tsum_add hplogZ_summable, tsum_mul_left,
      show (fun a => p a * Real.log Z) = (fun a => Real.log Z * p a) by
        funext a
        ring, tsum_mul_left]
  have hpsum := ρ.spectralTrace_op_eq_one
  change ∑' a : EigenvectorIndex ρ.op, p a = 1 at hpsum
  rw [hphsum, hpsum] at hsum_eq
  have hqZsum_le : ∑' a, q a / Z ≤ 1 :=
    tsum_div_le_one hq_summable_and_le.2 hZpos
  have hEntropyTarget :
      (vonNeumannEntropy ρ).toReal = β * energyExpValue ρ Hop + Real.log Z := by
    have hfree' := hfree
    change energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal =
      -(1 / β) * Real.log Z at hfree'
    field_simp [hβ] at hfree'
    linarith
  have hnMLTarget :
      ∑' a, Real.negMulLog (p a) = β * energyExpValue ρ Hop + Real.log Z := by
    rw [← hToReal]
    exact hEntropyTarget
  have htarget_le_B :
      β * energyExpValue ρ Hop + Real.log Z ≤
        ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) := by
    rw [← hnMLTarget]
    exact hsum_le
  have hqZsum_ge : 1 ≤ ∑' a, q a / Z := by
    rw [hsum_eq] at htarget_le_B
    nlinarith
  have hqZsum_eq : ∑' a, q a / Z = 1 :=
    le_antisymm hqZsum_le hqZsum_ge
  have hBTarget :
      ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) =
        β * energyExpValue ρ Hop + Real.log Z := by
    rw [hsum_eq, hqZsum_eq]
    ring
  have hnML_eq_B :
      ∑' a, Real.negMulLog (p a) =
        ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) :=
    hnMLTarget.trans hBTarget.symm
  have hterm_eq : ∀ a, Real.negMulLog (p a) =
      β * (p a * h a) + p a * Real.log Z - p a + q a / Z := by
    intro a
    apply le_antisymm (hbound a)
    by_contra hnot
    have hlt : Real.negMulLog (p a) <
        β * (p a * h a) + p a * Real.log Z - p a + q a / Z :=
      lt_of_not_ge hnot
    have hsumlt := Summable.tsum_lt_tsum hbound hlt hnML_summable hB_summable
    exact (ne_of_lt hsumlt) hnML_eq_B
  have hp_pos : ∀ a, 0 < p a := fun a => by
    exact lt_of_le_of_ne (ρ.eigenvalue_nonneg a) (Ne.symm a.1.2)
  have hscalar : ∀ a, p a = q a / Z ∧ -Real.log (q a) = β * h a := fun a => by
    apply (negMulLog_bound_eq_iff (hp_pos a) (hqpos a) hZpos (hstep2 a)).mp
    calc
      Real.negMulLog (p a) =
          β * (p a * h a) + p a * Real.log Z - p a + q a / Z := hterm_eq a
      _ = p a * (β * h a) + p a * Real.log Z - p a + q a / Z := by ring
  have hpeq : ∀ a, p a = q a / Z := fun a => (hscalar a).1
  have hpeierls : ∀ a, Real.exp (-β * h a) = q a := fun a => by
    have hlogeq : Real.log (q a) = -β * h a := by
      linarith [(hscalar a).2]
    calc
      Real.exp (-β * h a) = Real.exp (Real.log (q a)) := by rw [hlogeq]
      _ = q a := Real.exp_log (hqpos a)
  have hqsum_eq : ∑' a, q a = Z := by
    have hdiv : (∑' a, q a) / Z = 1 := by
      rw [div_eq_mul_inv]
      rw [← tsum_mul_right]
      simpa [div_eq_mul_inv] using hqZsum_eq
    exact (div_eq_one_iff_eq hZpos.ne').mp hdiv
  refine ⟨?_, ?_, ?_⟩
  · simpa [d, q, Z] using hqsum_eq
  · intro a
    simpa [p, q, Z, d] using hpeq a
  · intro a
    simpa [h, q, d] using hpeierls a

end QuantumTheory

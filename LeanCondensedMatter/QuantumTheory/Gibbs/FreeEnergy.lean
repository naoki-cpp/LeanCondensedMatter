import LeanCondensedMatter.QuantumTheory.Gibbs.EnergyExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.State
import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubov
import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled

/-!
# Helmholtz free-energy inequality

For any density operator, bounded Hamiltonian, and positive inverse temperature, the Helmholtz free
energy is bounded below by the free energy determined by the spectral trace of `e^{-βH}`.
-/

/-- From `exp(-u) ≤ q`, obtain `-log q ≤ u`. -/
theorem neg_log_le_of_exp_le {u q : ℝ} (hq : Real.exp (-u) ≤ q) : -Real.log q ≤ u := by
  have hlog := Real.log_le_log (Real.exp_pos _) hq
  rw [Real.log_exp] at hlog
  linarith

/-- Gibbs' scalar inequality. -/
theorem gibbs_scalar_ineq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x + x - y ≤ -x * Real.log y := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · simp only [Real.negMulLog, ← hx0]
    nlinarith
  · have hxy : 0 < y / x := div_pos hy hx0
    have hlog := Real.log_le_sub_one_of_pos hxy
    rw [Real.log_div hy.ne' hx0.ne'] at hlog
    have hcancel : x * (y / x) = y := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hlog hx0.le
    simp only [Real.negMulLog]
    nlinarith [hmul, hcancel]

/-- Combine `gibbs_scalar_ineq` with a bound on `-log q`. -/
theorem negMulLog_le_of_neg_log_le {p q Z u : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hZ : 0 < Z)
    (hlog : -Real.log q ≤ u) :
    Real.negMulLog p ≤ p * u + p * Real.log Z - p + q / Z := by
  have hqZpos : 0 < q / Z := div_pos hq hZ
  have hgibbs := gibbs_scalar_ineq p (q / Z) hp hqZpos
  have hlogdiv : Real.log (q / Z) = Real.log q - Real.log Z := Real.log_div hq.ne' hZ.ne'
  have hmul : -p * Real.log q ≤ p * u := by
    have := mul_le_mul_of_nonneg_left hlog hp
    nlinarith [this]
  nlinarith [hgibbs, hlogdiv, hmul]

/-- The sum of `q i / Z` is at most one when `∑' i, q i ≤ Z` and `Z > 0`. -/
theorem tsum_div_le_one {ι : Type*} {q : ι → ℝ} {Z : ℝ}
    (hsum : ∑' i, q i ≤ Z) (hZ : 0 < Z) : ∑' i, q i / Z ≤ 1 := by
  rw [show (∑' i, q i / Z) = (∑' i, q i) * Z⁻¹ by
    rw [← tsum_mul_right]; exact tsum_congr fun i => div_eq_mul_inv _ _]
  calc (∑' i, q i) * Z⁻¹ ≤ Z * Z⁻¹ := mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hZ.le)
    _ = 1 := mul_inv_cancel₀ hZ.ne'

namespace QuantumTheory

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Comparison test packaged with `tsum` monotonicity. -/
theorem summable_and_tsum_le_of_nonneg_of_le {ι : Type*} {f g : ι → ℝ}
    (hf_nonneg : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) (hg : Summable g) :
    Summable f ∧ ∑' i, f i ≤ ∑' i, g i :=
  have hf : Summable f := Summable.of_nonneg_of_le hf_nonneg hfg hg
  ⟨hf, hf.tsum_mono hg hfg⟩

/-- The spectral trace of the unnormalized Gibbs operator is positive when nonzero. -/
theorem spectralTrace_gibbsOp_pos (Hop : Observable H) (β : ℝ)
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) : 0 < spectralTrace (gibbsOp Hop β) :=
  (ContinuousLinearMap.trace_nonneg (gibbsOp_isPositive Hop β).toLinearMap).lt_of_ne
    (Ne.symm hZ)

/-- Peierls–Bogoliubov in lossless diagonal-expectation form against a unit vector. -/
theorem exp_neg_beta_energy_le_gibbs_diagonal (Hop : Observable H) (β : ℝ) (v : H)
    (hv : ‖v‖ = 1) :
    Real.exp (-β * diagonalExpectationValue Hop.1 Hop.2 v) ≤
      diagonalExpectationValue (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v := by
  have hpb := gibbs_peierls_bogoliubov Hop.1 Hop.2 β v hv
  change (Real.exp (-β * diagonalExpectationValue Hop.1 Hop.2 v) : ℂ) ≤
    inner ℂ (gibbsOp Hop β v) v at hpb
  rw [← coe_diagonalExpectationValue
    (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v] at hpb
  exact_mod_cast hpb

/-- The eigenvalue-weighted lossless energy-expectation sum is summable, with total
`energyExpValue ρ Hop`. -/
theorem summable_eigenvalue_mul_energy_and_tsum (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op =>
        a.1.1 * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a)) ∧
      ∑' a : EigenvectorIndex ρ.op,
          a.1.1 * diagonalExpectationValue Hop.1 Hop.2
            (eigenvectorFamily ρ.spectralTraceClass.compact a) =
        energyExpValue ρ Hop := by
  have hsComplex : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        ((a.1.1 * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a) : ℝ) : ℂ))
      (energyExpValue ρ Hop : ℂ) := by
    have hs := (ρ.summable_observableExpectation_term Hop).hasSum
    rw [← ρ.expectation_apply Hop.1, ρ.expectation_observable] at hs
    simpa only [Complex.ofReal_mul, coe_diagonalExpectationValue_right, energyExpValue] using hs
  have hsReal : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        a.1.1 * diagonalExpectationValue Hop.1 Hop.2
          (eigenvectorFamily ρ.spectralTraceClass.compact a))
      (energyExpValue ρ Hop) := by
    exact_mod_cast hsComplex
  exact ⟨hsReal.summable, hsReal.tsum_eq⟩

/-- The Gibbs–Klein / Helmholtz free-energy inequality. -/
theorem helmholtzFreeEnergy_ge_and_entropy_ne_top (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) ≤
        energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
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
    have hb := negMulLog_le_of_neg_log_le (p := p a) (q := q a) (Z := Z) (u := β * h a)
      (ρ.eigenvalue_nonneg a) (hqpos a) hZpos (hstep2 a)
    nlinarith [hb]
  have hp_summable : Summable p :=
    ρ.spectralTraceClass.summable.congr (fun b => abs_of_nonneg (ρ.eigenvalue_nonneg b))
  obtain ⟨hph_summable, hphsum⟩ := summable_eigenvalue_mul_energy_and_tsum ρ Hop
  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z := by
    have hbound := hGibbs.sum_diagonalExpectationValue_le_trace
      (gibbsOp_isPositive Hop β).toLinearMap hd_orth
    rw [hGibbs.trace_eq_spectralTrace] at hbound
    simpa [Z, hq_def] using hbound
  have hqZ_summable : Summable (fun a => q a / Z) := hq_summable_and_le.1.div_const Z
  have hplogZ_summable : Summable (fun a => p a * Real.log Z) := hp_summable.mul_right _
  have hB_summable : Summable
      (fun a => β * (p a * h a) + p a * Real.log Z - p a + q a / Z) :=
    ((hph_summable.mul_left β).add hplogZ_summable).sub hp_summable |>.add hqZ_summable
  have hnegMulLog_nonneg : ∀ a, 0 ≤ Real.negMulLog (p a) :=
    fun a => Real.negMulLog_nonneg (ρ.eigenvalue_nonneg a) (ρ.eigenvalue_le_one a)
  obtain ⟨hnML_summable, hsum_le⟩ :=
    summable_and_tsum_le_of_nonneg_of_le hnegMulLog_nonneg hbound hB_summable
  obtain ⟨hEntropyNeTop, hToReal⟩ :=
    vonNeumannEntropy_ne_top_and_toReal_eq_tsum ρ hnML_summable
  refine ⟨hEntropyNeTop, ?_⟩
  have hsum_eq : ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) =
      β * (∑' a, p a * h a) + Real.log Z * (∑' a, p a) - (∑' a, p a) + ∑' a, q a / Z := by
    rw [(((hph_summable.mul_left β).add hplogZ_summable).sub hp_summable).tsum_add
      hqZ_summable, ((hph_summable.mul_left β).add hplogZ_summable).tsum_sub hp_summable,
      (hph_summable.mul_left β).tsum_add hplogZ_summable, tsum_mul_left,
      show (fun a => p a * Real.log Z) = (fun a => Real.log Z * p a) by
        funext a
        ring, tsum_mul_left]
  have hpsum := ρ.spectralTrace_op_eq_one
  change ∑' a : EigenvectorIndex ρ.op, p a = 1 at hpsum
  have hqZsum_le : ∑' a, q a / Z ≤ 1 :=
    tsum_div_le_one hq_summable_and_le.2 hZpos
  rw [hphsum, hpsum] at hsum_eq
  rw [hToReal]
  have hfinal : ∑' a, Real.negMulLog (p a) ≤ β * energyExpValue ρ Hop + Real.log Z := by
    calc ∑' a, Real.negMulLog (p a)
        ≤ β * energyExpValue ρ Hop + Real.log Z * 1 - 1 + ∑' a, q a / Z := by
          rw [← hsum_eq]
          exact hsum_le
      _ ≤ β * energyExpValue ρ Hop + Real.log Z * 1 - 1 + 1 := by linarith [hqZsum_le]
      _ = β * energyExpValue ρ Hop + Real.log Z := by ring
  have hβinv : 0 < 1 / β := by positivity
  have hcancel : (1 / β) * (β * energyExpValue ρ Hop) = energyExpValue ρ Hop := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hfinal hβinv.le
  rw [mul_add, hcancel] at hmul
  linarith [hmul]

end QuantumTheory

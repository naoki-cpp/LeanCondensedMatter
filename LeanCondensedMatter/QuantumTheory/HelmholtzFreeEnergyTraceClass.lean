import LeanCondensedMatter.QuantumTheory.EnergyExpValueTraceClass
import LeanCondensedMatter.QuantumTheory.GibbsStateTraceClass
import LeanCondensedMatter.QuantumTheory.EntropyTraceClass
import LeanCondensedMatter.Analysis.PeierlsBogoliubov

/-!
# The Gibbs–Klein / Helmholtz free-energy inequality (infinite dimensions)

Extends `QuantumTheory.helmholtzFreeEnergy_ge` (`QuantumTheory/Entropy.lean`) beyond
finite-dimensional `H`: for any density operator `ρ`, Hamiltonian `Hop`, and inverse temperature
`β > 0`, the Helmholtz free energy `F[ρ] = Tr[ρĤ] - (1/β)·S[ρ]` is bounded below by
`-(1/β)·ln Z(β)`, the free energy of the (unnormalized) Gibbs operator `e^{-βH}`'s own state.

**This file is additive, not a replacement.**

See the file docstring of `LeanCondensedMatter/Analysis/PeierlsBogoliubov.lean` and the roadmap
notes (`notes/roadmaps/quantum-theory-foundations.md`, `notes/roadmaps/operator-algebra.md`) for
the full derivation this file implements.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Gibbs' scalar inequality.** For `x ≥ 0` and `y > 0`,
`-x ln x + x - y ≤ -x ln y`. The key elementary convexity fact (of `t ↦ t ln t - t`) driving the
Gibbs–Klein argument, reduced here to `Real.log_le_sub_one_of_pos` applied to `y / x`. -/
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

/-- **A density operator's eigenvalues are at most `1`.** From `Σᵢ pᵢ = 1` and `pᵢ ≥ 0`, each
`pᵢ` is at most the total. Needed for `Real.negMulLog_nonneg`. -/
theorem eigenvalue_le_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) : a.1.1 ≤ 1 := by
  have hsum : Summable (fun b : EigenvectorIndex ρ.op => b.1.1) :=
    ρ.traceClass.congr (fun b => abs_of_nonneg (eigenvalue_nonneg ρ b))
  have hle := hsum.le_tsum a (fun j _ => eigenvalue_nonneg ρ j)
  have heq : ∑' b : EigenvectorIndex ρ.op, b.1.1 = 1 := ρ.trace_eq_one
  rwa [heq] at hle

/-- **The Gibbs–Klein / Helmholtz free-energy inequality (infinite-dimensional), and
`vonNeumannEntropy ρ ≠ ⊤` as a byproduct.** Packaged as one lemma since both conclusions share
almost all of the same summability/inequality bookkeeping: given a density operator `ρ`,
Hamiltonian `Hop`, `β > 0`, and the hypotheses needed to form `gibbsState Hop β` (compactness,
trace-class-ness, and nonzero trace of the unnormalized Gibbs operator `e^{-βH}`), the entropy sum
`Σᵢ negMulLog(pᵢ)` (`pᵢ` = `ρ`'s eigenvalues) is finite, and its value (as a real number) satisfies
the free-energy bound against `energyExpValue`.

**Proof sketch.** For each `i`, `gibbs_peierls_bogoliubov` gives `exp(-β hᵢ) ≤ qᵢ` where
`hᵢ = ⟪eᵢ,Hop eᵢ⟫.re` and `qᵢ = ⟪eᵢ, gibbsOp eᵢ⟫.re` (so in particular `qᵢ > 0`). Gibbs' scalar
inequality (`gibbs_scalar_ineq`) applied to `x = pᵢ`, `y = qᵢ/Z` (`Z = trace htc > 0`), combined
with `-ln qᵢ ≤ β hᵢ` (from monotonicity of `ln` on the Peierls–Bogoliubov bound), gives the
termwise bound `negMulLog(pᵢ) ≤ β pᵢ hᵢ + pᵢ ln Z - pᵢ + qᵢ/Z`. Summing over `i` (using
`sum_inner_apply_le_trace` for `Σqᵢ ≤ Z` and `ρ.trace_eq_one` for `Σpᵢ = 1`) closes the
argument. -/
theorem helmholtzFreeEnergy_ge_and_entropy_ne_top (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) (hcompact : IsCompactOperator (gibbsOp Hop β))
    (htc : IsTraceClass (gibbsOp Hop β)) (hZ : trace htc ≠ 0) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      -(1 / β) * Real.log (trace htc) ≤
        energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
  set d := eigenvectorFamily ρ.compact with hd_def
  set p : EigenvectorIndex ρ.op → ℝ := fun a => a.1.1 with hp_def
  set h : EigenvectorIndex ρ.op → ℝ := fun a => (inner ℂ (d a) (Hop.1 (d a)) : ℂ).re with hh_def
  set q : EigenvectorIndex ρ.op → ℝ :=
    fun a => (inner ℂ (d a) (gibbsOp Hop β (d a)) : ℂ).re with hq_def
  set Z : ℝ := trace htc with hZ_def
  have hZnonneg : 0 ≤ Z :=
    ContinuousLinearMap.trace_nonneg htc (gibbsOp_isPositive Hop β).toLinearMap
  have hZpos : 0 < Z := hZnonneg.lt_of_ne (Ne.symm hZ)
  have hHopSym : (Hop.1 : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp Hop.2
  have hGibbsSym : ((gibbsOp Hop β : H →L[ℂ] H) : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gibbsOp_isPositive Hop β).isSelfAdjoint
  have hd_orth : Orthonormal ℂ d := orthonormal_eigenvectorFamily ρ.compact ρ.isSymmetric
  have hd_unit : ∀ a, ‖d a‖ = 1 := eigenvectorFamily_norm_eq_one ρ
  -- Step 1: pointwise Peierls–Bogoliubov, in `h`/`q` form.
  have hstep1 : ∀ a, Real.exp (-β * h a) ≤ q a := by
    intro a
    have hpb := gibbs_peierls_bogoliubov Hop.1 Hop.2 β (d a) (hd_unit a)
    have heqL : (inner ℂ (Hop.1 (d a)) (d a) : ℂ).re = h a := by
      rw [hh_def]; congr 1; exact hHopSym (d a) (d a)
    have heqR : (inner ℂ (cfc (R := ℝ) (fun x => Real.exp (-β * x)) Hop.1 (d a)) (d a) : ℂ).re
        = q a := by
      rw [hq_def]
      change
        (inner ℂ (gibbsOp Hop β (d a)) (d a) : ℂ).re = (inner ℂ (d a) (gibbsOp Hop β (d a)) : ℂ).re
      congr 1; exact hGibbsSym (d a) (d a)
    rw [heqL, heqR] at hpb
    exact hpb
  have hqpos : ∀ a, 0 < q a := fun a => (Real.exp_pos _).trans_le (hstep1 a)
  -- Step 2: `-ln q ≤ β h` from monotonicity of `log`.
  have hstep2 : ∀ a, -Real.log (q a) ≤ β * h a := by
    intro a
    have hlog := Real.log_le_log (Real.exp_pos _) (hstep1 a)
    rw [Real.log_exp] at hlog
    linarith
  -- Step 3: the termwise bound `negMulLog (p a) ≤ β * p a * h a + p a * log Z - p a + q a / Z`.
  have hbound : ∀ a, Real.negMulLog (p a) ≤ β * (p a * h a) + p a * Real.log Z - p a + q a / Z := by
    intro a
    have hpnn : 0 ≤ p a := eigenvalue_nonneg ρ a
    have hqZpos : 0 < q a / Z := div_pos (hqpos a) hZpos
    have hgibbs := gibbs_scalar_ineq (p a) (q a / Z) hpnn hqZpos
    have hlogdiv : Real.log (q a / Z) = Real.log (q a) - Real.log Z :=
      Real.log_div (hqpos a).ne' hZpos.ne'
    have hstep2' : -(p a) * Real.log (q a) ≤ p a * (β * h a) := by
      have := mul_le_mul_of_nonneg_left (hstep2 a) hpnn
      nlinarith [this]
    nlinarith [hgibbs, hlogdiv, hstep2']
  -- Step 4: summability of the pieces of the bound.
  have hp_summable : Summable p :=
    ρ.traceClass.congr (fun b => abs_of_nonneg (eigenvalue_nonneg ρ b))
  have hph_summable : Summable (fun a => p a * h a) := by
    have hE := summable_energyExpValue_term ρ Hop
    have hre := Complex.reCLM.summable hE
    have heq : (fun a : EigenvectorIndex ρ.op =>
        Complex.reCLM (((p a : ℝ) : ℂ) * (inner ℂ (d a) (Hop.1 (d a)) : ℂ))) =
        (fun a => p a * h a) := by
      funext a
      change (((p a : ℝ) : ℂ) * (inner ℂ (d a) (Hop.1 (d a)) : ℂ)).re = p a * h a
      rw [Complex.re_ofReal_mul]
    rwa [heq] at hre
  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z :=
    ContinuousLinearMap.sum_inner_apply_le_trace hcompact hGibbsSym
      (gibbsOp_isPositive Hop β).toLinearMap htc hd_orth
  have hqZ_summable : Summable (fun a => q a / Z) := hq_summable_and_le.1.div_const Z
  have hplogZ_summable : Summable (fun a => p a * Real.log Z) := hp_summable.mul_right _
  have hB_summable : Summable
      (fun a => β * (p a * h a) + p a * Real.log Z - p a + q a / Z) :=
    ((hph_summable.mul_left β).add hplogZ_summable).sub hp_summable |>.add hqZ_summable
  -- Step 5: `negMulLog (p a)` is summable (comparison test).
  have hnegMulLog_nonneg : ∀ a, 0 ≤ Real.negMulLog (p a) :=
    fun a => Real.negMulLog_nonneg (eigenvalue_nonneg ρ a) (eigenvalue_le_one ρ a)
  have hnML_summable : Summable (fun a => Real.negMulLog (p a)) :=
    Summable.of_nonneg_of_le hnegMulLog_nonneg hbound hB_summable
  -- Step 6: `vonNeumannEntropy ρ = ofReal (Σ negMulLog (p a))`, hence finite.
  have hEntropyEq : vonNeumannEntropy ρ = ENNReal.ofReal (∑' a, Real.negMulLog (p a)) :=
    (ENNReal.ofReal_tsum_of_nonneg hnegMulLog_nonneg hnML_summable).symm
  have hEntropyNeTop : vonNeumannEntropy ρ ≠ ⊤ := by
    rw [hEntropyEq]; exact ENNReal.ofReal_ne_top
  have hS_nonneg : 0 ≤ ∑' a, Real.negMulLog (p a) := tsum_nonneg hnegMulLog_nonneg
  have hToReal : (vonNeumannEntropy ρ).toReal = ∑' a, Real.negMulLog (p a) := by
    rw [hEntropyEq, ENNReal.toReal_ofReal hS_nonneg]
  refine ⟨hEntropyNeTop, ?_⟩
  -- Step 7: sum the termwise bound.
  have hsum_le : ∑' a, Real.negMulLog (p a) ≤
      ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) :=
    hnML_summable.tsum_mono hB_summable hbound
  have hsum_eq : ∑' a, (β * (p a * h a) + p a * Real.log Z - p a + q a / Z) =
      β * (∑' a, p a * h a) + Real.log Z * (∑' a, p a) - (∑' a, p a) + ∑' a, q a / Z := by
    rw [(((hph_summable.mul_left β).add hplogZ_summable).sub hp_summable).tsum_add
      hqZ_summable, ((hph_summable.mul_left β).add hplogZ_summable).tsum_sub hp_summable,
      (hph_summable.mul_left β).tsum_add hplogZ_summable, tsum_mul_left,
      show (fun a => p a * Real.log Z) = (fun a => Real.log Z * p a) by
        funext a; ring, tsum_mul_left]
  have hpsum : ∑' a, p a = 1 := ρ.trace_eq_one
  have hphsum : ∑' a, p a * h a = energyExpValue ρ Hop := by
    have hE := summable_energyExpValue_term ρ Hop
    rw [show energyExpValue ρ Hop =
        (∑' a, ((p a : ℝ) : ℂ) * (inner ℂ (d a) (Hop.1 (d a)) : ℂ)).re from rfl,
      Complex.re_tsum hE]
    congr 1
    funext a
    rw [Complex.re_ofReal_mul]
  have hqZsum_le : ∑' a, q a / Z ≤ 1 := by
    have : ∑' a, q a / Z = (∑' a, q a) * Z⁻¹ := by
      rw [← tsum_mul_right]
      exact tsum_congr fun a => div_eq_mul_inv _ _
    rw [this]
    have := mul_le_mul_of_nonneg_right hq_summable_and_le.2 (inv_nonneg.mpr hZnonneg)
    calc (∑' a, q a) * Z⁻¹ ≤ Z * Z⁻¹ := this
      _ = 1 := mul_inv_cancel₀ hZpos.ne'
  rw [hphsum, hpsum] at hsum_eq
  rw [hToReal]
  have hfinal : ∑' a, Real.negMulLog (p a) ≤ β * energyExpValue ρ Hop + Real.log Z := by
    calc ∑' a, Real.negMulLog (p a)
        ≤ β * energyExpValue ρ Hop + Real.log Z * 1 - 1 + ∑' a, q a / Z := by
          rw [← hsum_eq]; exact hsum_le
      _ ≤ β * energyExpValue ρ Hop + Real.log Z * 1 - 1 + 1 := by linarith [hqZsum_le]
      _ = β * energyExpValue ρ Hop + Real.log Z := by ring
  have hβinv : 0 < 1 / β := by positivity
  have hcancel : (1 / β) * (β * energyExpValue ρ Hop) = energyExpValue ρ Hop := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hfinal hβinv.le
  rw [mul_add, hcancel] at hmul
  linarith [hmul]

end QuantumTheory.TraceClass

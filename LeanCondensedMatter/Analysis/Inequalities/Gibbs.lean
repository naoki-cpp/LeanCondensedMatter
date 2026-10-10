import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar and summable-family Gibbs inequalities

Entropy comparison for normalized nonnegative real families, with explicit summability,
positive comparison weights, and logarithmic energy bounds.
-/

namespace Real

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


/-- Equality in Gibbs' scalar inequality holds exactly on the diagonal `x = y`. -/
theorem gibbs_scalar_ineq_eq_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x + x - y = -x * Real.log y ↔ x = y := by
  constructor
  · intro heq
    by_contra hxy
    have hlt : Real.negMulLog x + x - y < -x * Real.log y := by
      rcases eq_or_lt_of_le hx with hx0 | hx0
      · subst x
        simp only [Real.negMulLog]
        linarith
      · have hratio_pos : 0 < y / x := div_pos hy hx0
        have hratio_ne : y / x ≠ 1 := by
          intro hratio
          apply hxy
          exact ((div_eq_one_iff_eq hx0.ne').mp hratio).symm
        have hlog := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
        rw [Real.log_div hy.ne' hx0.ne'] at hlog
        have hcancel : x * (y / x) = y := by field_simp
        have hmul := mul_lt_mul_of_pos_left hlog hx0
        simp only [Real.negMulLog]
        nlinarith [hmul, hcancel]
    exact (ne_of_lt hlt) heq
  · rintro rfl
    simp [Real.negMulLog]

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

/-- Comparison test packaged with `tsum` monotonicity. -/
private theorem summable_and_tsum_le_of_nonneg_of_le {ι : Type*} {f g : ι → ℝ}
    (hf_nonneg : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) (hg : Summable g) :
    Summable f ∧ ∑' i, f i ≤ ∑' i, g i :=
  have hf : Summable f := Summable.of_nonneg_of_le hf_nonneg hfg hg
  ⟨hf, hf.tsum_mono hg hfg⟩


/-- The Gibbs comparison series is summable whenever the normalized probability family,
energy term, and comparison weights are summable. Its total separates into energy, normalization,
and comparison-weight contributions. -/
theorem summable_gibbsComparison_and_tsum_eq
    {ι : Type*} (p q energy : ι → ℝ) (β Z : ℝ)
    (hp_hasSum : HasSum p 1)
    (henergy : Summable fun i => p i * energy i)
    (hq_summable : Summable q) :
    Summable
        (fun i => β * (p i * energy i) + p i * Real.log Z - p i + q i / Z) ∧
      (∑' i, (β * (p i * energy i) + p i * Real.log Z - p i + q i / Z)) =
        β * (∑' i, p i * energy i) + Real.log Z - 1 + ∑' i, q i / Z := by
  have hp_summable : Summable p := hp_hasSum.summable
  have hqZ_summable : Summable (fun i => q i / Z) :=
    hq_summable.div_const Z
  have hplogZ_summable : Summable (fun i => p i * Real.log Z) :=
    hp_summable.mul_right _
  have hB_summable : Summable
      (fun i => β * (p i * energy i) + p i * Real.log Z - p i + q i / Z) :=
    ((henergy.mul_left β).add hplogZ_summable).sub hp_summable |>.add hqZ_summable
  refine ⟨hB_summable, ?_⟩
  rw [(((henergy.mul_left β).add hplogZ_summable).sub hp_summable).tsum_add
    hqZ_summable, ((henergy.mul_left β).add hplogZ_summable).tsum_sub hp_summable,
    (henergy.mul_left β).tsum_add hplogZ_summable, tsum_mul_left,
    show (fun i => p i * Real.log Z) = (fun i => Real.log Z * p i) by
      funext i
      ring, tsum_mul_left, hp_hasSum.tsum_eq]
  ring

/-- Countable Gibbs entropy bound for a normalized nonnegative family. The comparison weights need
only have total mass at most `Z`; the logarithmic estimate supplies the energy term. -/
theorem summable_negMulLog_and_tsum_le_gibbs
    {ι : Type*} (p q energy : ι → ℝ) (β Z : ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_hasSum : HasSum p 1)
    (henergy : Summable fun i => p i * energy i)
    (hq_summable : Summable q)
    (hq_tsum_le : ∑' i, q i ≤ Z)
    (hq_pos : ∀ i, 0 < q i)
    (hZ : 0 < Z)
    (hlog : ∀ i, -Real.log (q i) ≤ β * energy i) :
    Summable (fun i => Real.negMulLog (p i)) ∧
      ∑' i, Real.negMulLog (p i) ≤
        β * (∑' i, p i * energy i) + Real.log Z := by
  have hp_summable : Summable p := hp_hasSum.summable
  obtain ⟨hB_summable, hBsum⟩ :=
    summable_gibbsComparison_and_tsum_eq p q energy β Z hp_hasSum henergy hq_summable
  have hbound : ∀ i, Real.negMulLog (p i) ≤
      β * (p i * energy i) + p i * Real.log Z - p i + q i / Z := by
    intro i
    have hb := negMulLog_le_of_neg_log_le
      (p := p i) (q := q i) (Z := Z) (u := β * energy i)
      (hp_nonneg i) (hq_pos i) hZ (hlog i)
    nlinarith [hb]
  have hp_le_one : ∀ i, p i ≤ 1 := by
    intro i
    have hle := hp_summable.le_tsum i (fun j _ => hp_nonneg j)
    rwa [hp_hasSum.tsum_eq] at hle
  have hnegMulLog_nonneg : ∀ i, 0 ≤ Real.negMulLog (p i) :=
    fun i => Real.negMulLog_nonneg (hp_nonneg i) (hp_le_one i)
  obtain ⟨hnegMulLog_summable, hsum_le⟩ :=
    summable_and_tsum_le_of_nonneg_of_le hnegMulLog_nonneg hbound hB_summable
  have hqZsum_le : ∑' i, q i / Z ≤ 1 :=
    tsum_div_le_one hq_tsum_le hZ
  have hfinal :
      ∑' i, Real.negMulLog (p i) ≤
        β * (∑' i, p i * energy i) + Real.log Z := by
    calc
      ∑' i, Real.negMulLog (p i) ≤
          ∑' i, (β * (p i * energy i) + p i * Real.log Z - p i + q i / Z) :=
        hsum_le
      _ = β * (∑' i, p i * energy i) + Real.log Z - 1 + ∑' i, q i / Z :=
        hBsum
      _ ≤ β * (∑' i, p i * energy i) + Real.log Z - 1 + 1 := by
        linarith
      _ = β * (∑' i, p i * energy i) + Real.log Z := by ring
  exact ⟨hnegMulLog_summable, hfinal⟩

end Real

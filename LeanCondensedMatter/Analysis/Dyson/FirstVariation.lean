import LeanCondensedMatter.Analysis.Dyson.Bounds
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# First-variation bounds for generic Dyson evolution

This module isolates the quantitative estimate needed to differentiate the bounded Dyson evolution
with respect to its scalar coupling. After removing the zeroth and first weighted coefficients, the
remaining series starts at order two and is controlled termwise by the shifted factorial majorant.

The theorem remains in the state-independent `Analysis.Dyson` layer. Physical coupling conventions,
Planck's constant, and interaction-picture observables belong to downstream `QuantumTheory`
specializations.
-/

namespace Dyson

open Filter Set
open scoped Topology

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The part of the bounded Dyson evolution beyond first order is controlled by the corresponding
shifted factorial-majorant series. -/
theorem norm_evolution_sub_one_add_term_one_le_of_bound
    (V : ℝ → A) {β M : ℝ}
    (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖evolution V lam τ - (1 + term V lam τ 1)‖ ≤
      ∑' n : ℕ, majorant (‖lam‖ * M) τ (n + 2) := by
  have htail :
      HasSum (fun n : ℕ => term V lam τ (n + 2))
        (evolution V lam τ - ∑ n ∈ Finset.range 2, term V lam τ n) :=
    (hasSum_nat_add_iff' 2).2
      (hasSum_evolution_of_bound V hOne hM hV lam hτ)
  have hmajorant :
      Summable (fun n : ℕ => majorant (‖lam‖ * M) τ (n + 2)) :=
    (summable_nat_add_iff 2).2 (summable_majorant (‖lam‖ * M) τ)
  have hbound := htail.norm_le_of_bounded hmajorant.hasSum fun n =>
    norm_term_le_of_bound V hOne hM hV lam (n + 2) hτ
  simpa [Finset.sum_range_succ] using hbound

/-- On the unit coupling ball, each shifted majorant term factors out two powers of the coupling
norm. -/
theorem majorant_norm_mul_le_sq_mul_majorant
    {r M τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hM : 0 ≤ M) (hτ : 0 ≤ τ) (n : ℕ) :
    majorant (r * M) τ (n + 2) ≤ r ^ 2 * majorant M τ (n + 2) := by
  have hrn : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1
  have hscale :
      0 ≤ (Nat.factorial (n + 2) : ℝ)⁻¹ * (M * τ) ^ (n + 2) := by
    positivity
  unfold majorant
  calc
    (Nat.factorial (n + 2) : ℝ)⁻¹ * ((r * M) * τ) ^ (n + 2) =
        (r ^ n * r ^ 2) *
          ((Nat.factorial (n + 2) : ℝ)⁻¹ * (M * τ) ^ (n + 2)) := by
      rw [show (r * M) * τ = r * (M * τ) by ring, mul_pow, pow_add]
      ring
    _ ≤ (1 * r ^ 2) *
          ((Nat.factorial (n + 2) : ℝ)⁻¹ * (M * τ) ^ (n + 2)) := by
      gcongr
    _ = r ^ 2 *
          ((Nat.factorial (n + 2) : ℝ)⁻¹ * (M * τ) ^ (n + 2)) := by ring

/-- On the unit coupling ball, the complete Dyson remainder beyond first order is quadratic in the
coupling norm, with an explicit coupling-independent factorial tail. -/
theorem norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
    (V : ℝ → A) {β M : ℝ}
    (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) (hlam : ‖lam‖ ≤ 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖evolution V lam τ - (1 + term V lam τ 1)‖ ≤
      ‖lam‖ ^ 2 * ∑' n : ℕ, majorant M τ (n + 2) := by
  refine (norm_evolution_sub_one_add_term_one_le_of_bound
    V hOne hM hV lam hτ).trans ?_
  have hleft : Summable (fun n : ℕ => majorant (‖lam‖ * M) τ (n + 2)) :=
    (summable_nat_add_iff 2).2 (summable_majorant (‖lam‖ * M) τ)
  have hbase : Summable (fun n : ℕ => majorant M τ (n + 2)) :=
    (summable_nat_add_iff 2).2 (summable_majorant M τ)
  have hright : Summable (fun n : ℕ => ‖lam‖ ^ 2 * majorant M τ (n + 2)) :=
    hbase.mul_left _
  calc
    (∑' n : ℕ, majorant (‖lam‖ * M) τ (n + 2)) ≤
        ∑' n : ℕ, ‖lam‖ ^ 2 * majorant M τ (n + 2) :=
      hleft.tsum_le_tsum
        (fun n => majorant_norm_mul_le_sq_mul_majorant
          (norm_nonneg lam) hlam hM hτ.1 n)
        hright
    _ = ‖lam‖ ^ 2 * ∑' n : ℕ, majorant M τ (n + 2) := by
      rw [tsum_mul_left]

/-- A Dyson evolution whose complex scalar coupling depends linearly on a real parameter is
differentiable at zero. The derivative is the exact first Dyson coefficient multiplied by the
linear coupling constant. -/
theorem hasDerivAt_evolution_linear_coupling_zero_of_bound
    (V : ℝ → A) {β M τ : ℝ}
    (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (κ : ℂ) :
    HasDerivAt
      (fun lam : ℝ => evolution V ((lam : ℂ) * κ) τ)
      ((-κ) • ∫ σ in (0 : ℝ)..τ, V σ)
      0 := by
  rw [hasDerivAt_iff_tendsto]
  let C : ℝ := ∑' n : ℕ, majorant M τ (n + 2)
  have habs : Tendsto (fun lam : ℝ => |lam|) (𝓝 0) (𝓝 0) := by
    simpa [Real.norm_eq_abs] using (continuous_norm.tendsto (0 : ℝ))
  have hscaled : Tendsto (fun lam : ℝ => |lam| * ‖κ‖) (𝓝 0) (𝓝 0) := by
    simpa using habs.mul_const ‖κ‖
  have hsmall : ∀ᶠ lam : ℝ in 𝓝 0, |lam| * ‖κ‖ ≤ 1 := by
    have hevent : ∀ᶠ lam : ℝ in 𝓝 0, |lam| * ‖κ‖ < 1 :=
      hscaled (Iio_mem_nhds zero_lt_one)
    filter_upwards [hevent] with lam hlam
    exact hlam.le
  refine squeeze_zero'
    (g := fun lam : ℝ => |lam| * (‖κ‖ ^ 2 * C)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun lam =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · filter_upwards [hsmall] with lam hlam
    have hlam' : ‖((lam : ℂ) * κ)‖ ≤ 1 := by
      simpa using hlam
    have hrem := norm_evolution_sub_one_add_term_one_le_sq_mul_of_bound
      V hOne hM hV ((lam : ℂ) * κ) hlam' hτ
    have hlin :
        lam • ((-κ) • ∫ σ in (0 : ℝ)..τ, V σ) =
          term V ((lam : ℂ) * κ) τ 1 := by
      rw [term_one]
      change ((lam : ℂ) * (-κ)) • (∫ σ in (0 : ℝ)..τ, V σ) =
        (-((lam : ℂ) * κ)) • (∫ σ in (0 : ℝ)..τ, V σ)
      congr 1
      ring
    have hrem' :
        ‖evolution V ((lam : ℂ) * κ) τ -
            evolution V (((0 : ℝ) : ℂ) * κ) τ -
            lam • ((-κ) • ∫ σ in (0 : ℝ)..τ, V σ)‖ ≤
          (|lam| * ‖κ‖) ^ 2 * C := by
      rw [hlin]
      simpa [C, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem
    by_cases hlam0 : lam = 0
    · subst lam
      simp
    · have habs0 : |lam| ≠ 0 := abs_ne_zero.mpr hlam0
      calc
        ‖lam - 0‖⁻¹ *
            ‖evolution V ((lam : ℂ) * κ) τ -
              evolution V (((0 : ℝ) : ℂ) * κ) τ -
              (lam - 0) • ((-κ) • ∫ σ in (0 : ℝ)..τ, V σ)‖ ≤
            |lam|⁻¹ * ((|lam| * ‖κ‖) ^ 2 * C) := by
          simpa [Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left hrem' (inv_nonneg.mpr (abs_nonneg lam))
        _ = |lam| * (‖κ‖ ^ 2 * C) := by
          field_simp [habs0]
          <;> ring
  · simpa using habs.mul_const (‖κ‖ ^ 2 * C)

end
end Dyson

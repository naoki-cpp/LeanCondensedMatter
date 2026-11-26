import LeanCondensedMatter.Analysis.Dyson.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# Bounds, convergence and first variation for generic bounded Dyson coefficients

This module proves the analytic estimates for the dimension-independent Dyson recursion from
`Analysis.Dyson.Basic`. The interaction family is controlled by the canonical bounded-interaction
hypotheses on a compact nonnegative time interval; no finite-dimensional realization or choice-based
operator bound is used here.

The bound theorems retain the explicit weak assumption `‖1‖ ≤ 1` through
`Dyson.BoundedInteraction`. This is weaker than requiring `NormOneClass` and also covers
bounded-operator algebras on a trivial space, where the identity operator has norm zero.
-/

namespace Dyson

open Set

variable {A : Type*} [NormedRing A]

/-- Quantitative hypotheses for a bounded Dyson interaction on `[0, β]`.

The weak identity estimate `‖1‖ ≤ 1` is stored explicitly rather than requiring `NormOneClass`. -/
structure BoundedInteraction (V : ℝ → A) (β M : ℝ) : Prop where
  norm_one_le : ‖(1 : A)‖ ≤ 1
  bound_nonneg : 0 ≤ M
  interaction_norm_le : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M

/-- A bounded Dyson interaction together with the global continuity used by the Volterra theory. -/
structure ContinuousBoundedInteraction (V : ℝ → A) (β M : ℝ) : Prop
    extends BoundedInteraction V β M where
  interaction_continuous : Continuous V

/-- A continuous interaction on a nonnegative compact interval admits a uniform nonnegative bound.

The weak identity estimate is supplied explicitly so this does not require a stronger norm
typeclass. -/
theorem exists_continuousBoundedInteraction (V : ℝ → A) {β : ℝ}
    (hβ : 0 ≤ β) (hV : Continuous V) (hOne : ‖(1 : A)‖ ≤ 1) :
    ∃ M : ℝ, ContinuousBoundedInteraction V β M := by
  have hcont : Continuous (fun t : ℝ => ‖V t‖) := continuous_norm.comp hV
  obtain ⟨tmax, htmax, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hβ) hcont.continuousOn
  exact ⟨‖V tmax‖,
    { toBoundedInteraction :=
        { norm_one_le := hOne
          bound_nonneg := norm_nonneg _
          interaction_norm_le := fun t ht => hmax ht }
      interaction_continuous := hV }⟩

end Dyson

namespace Dyson

open Set

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Continuous interaction families have continuous generic Dyson coefficients. -/
theorem continuous_coeff {V : ℝ → A} (hV : Continuous V) (n : ℕ) :
    Continuous (coeff V n) := by
  induction n with
  | zero =>
      change Continuous (fun _ : ℝ => (1 : A))
      fun_prop
  | succ n ih =>
      rw [continuous_iff_continuousAt]
      intro τ
      have hIntegrand : Continuous (fun σ : ℝ => V σ * coeff V n σ) := hV.mul ih
      have hPrimitive :
          HasDerivAt
            (fun t : ℝ => ∫ σ in (0 : ℝ)..t, V σ * coeff V n σ)
            (V τ * coeff V n τ) τ :=
        intervalIntegral.integral_hasDerivAt_right
          (hIntegrand.intervalIntegrable 0 τ)
          hIntegrand.stronglyMeasurable.stronglyMeasurableAtFilter
          hIntegrand.continuousAt
      change ContinuousAt
        (fun t : ℝ => -∫ σ in (0 : ℝ)..t, V σ * coeff V n σ) τ
      exact hPrimitive.continuousAt.neg

/-- Perturbatively weighted Dyson coefficients are continuous in time. -/
theorem continuous_term {V : ℝ → A} (hV : Continuous V) (lam : ℂ) (n : ℕ) :
    Continuous (fun τ => term V lam τ n) := by
  exact continuous_const.smul (continuous_coeff hV n)

omit [CompleteSpace A] in
/-- The canonical bounded-interaction hypotheses imply the standard factorial estimate for all
generic Dyson coefficients on `[0, β]`. -/
theorem norm_coeff_le_of_bound {V : ℝ → A} {β M : ℝ}
    (h : BoundedInteraction V β M) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖coeff V n τ‖ ≤ majorant M τ n := by
  induction n generalizing τ with
  | zero => simpa using h.norm_one_le
  | succ n ih =>
      rw [coeff_succ, norm_neg]
      calc
        ‖∫ σ in (0 : ℝ)..τ, V σ * coeff V n σ‖ ≤
            ∫ σ in (0 : ℝ)..τ, M * majorant M σ n := by
          apply intervalIntegral.norm_integral_le_of_norm_le hτ.1
          · refine Filter.Eventually.of_forall fun σ hσ => ?_
            have hσβ : σ ∈ Icc (0 : ℝ) β := ⟨hσ.1.le, hσ.2.trans hτ.2⟩
            calc
              ‖V σ * coeff V n σ‖ ≤ ‖V σ‖ * ‖coeff V n σ‖ := norm_mul_le _ _
              _ ≤ M * majorant M σ n :=
                mul_le_mul (h.interaction_norm_le σ hσβ) (ih hσβ)
                  (norm_nonneg _) h.bound_nonneg
          · have hcont : Continuous (fun σ : ℝ => M * majorant M σ n) := by
              unfold majorant
              fun_prop
            exact hcont.intervalIntegrable 0 τ
        _ = majorant M τ (n + 1) := integral_mul_majorant M τ n

omit [CompleteSpace A] in
/-- The weighted `n`th coefficient is controlled by the factorial majorant with interaction bound
`‖λ‖ M`. -/
theorem norm_term_le_of_bound {V : ℝ → A} {β M : ℝ}
    (h : BoundedInteraction V β M)
    (lam : ℂ) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖term V lam τ n‖ ≤ majorant (‖lam‖ * M) τ n := by
  calc
    ‖term V lam τ n‖ = ‖lam‖ ^ n * ‖coeff V n τ‖ := by
      rw [term, norm_smul, norm_pow]
    _ ≤ ‖lam‖ ^ n * majorant M τ n :=
      mul_le_mul_of_nonneg_left (norm_coeff_le_of_bound h n hτ)
        (pow_nonneg (norm_nonneg lam) n)
    _ = majorant (‖lam‖ * M) τ n := by
      simp only [majorant]
      ring_nf

/-- The weighted generic Dyson coefficients are summable at each time in a bounded interval. -/
theorem summable_term_of_bound {V : ℝ → A} {β M : ℝ}
    (h : BoundedInteraction V β M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    Summable (term V lam τ) := by
  have hnorm : Summable (fun n : ℕ => ‖term V lam τ n‖) :=
    (summable_majorant (‖lam‖ * M) τ).of_nonneg_of_le
      (fun n => norm_nonneg _)
      (fun n => norm_term_le_of_bound h lam n hτ)
  exact hnorm.of_norm

/-- The defining series has sum `evolution` whenever the interaction is uniformly bounded. -/
theorem hasSum_evolution_of_bound {V : ℝ → A} {β M : ℝ}
    (h : BoundedInteraction V β M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    HasSum (term V lam τ) (evolution V lam τ) := by
  exact (summable_term_of_bound h lam hτ).hasSum

/-- On a bounded nonnegative interval, the generic Dyson series converges uniformly in norm. -/
theorem hasSumUniformlyOn_evolution_of_bound {V : ℝ → A} {β M : ℝ}
    (h : BoundedInteraction V β M) (lam : ℂ) :
    HasSumUniformlyOn
      (fun n τ => term V lam τ n)
      (fun τ => evolution V lam τ)
      (Icc (0 : ℝ) β) := by
  have hWeighted : 0 ≤ ‖lam‖ * M := mul_nonneg (norm_nonneg lam) h.bound_nonneg
  simpa only [evolution] using
    (HasSumUniformlyOn.of_norm_le_summable
      (f := fun n τ => term V lam τ n)
      (u := majorant (‖lam‖ * M) β)
      (summable_majorant (‖lam‖ * M) β)
      (fun n τ hτ =>
        (norm_term_le_of_bound h lam n hτ).trans
          (majorant_mono_time hWeighted hτ.1 hτ.2 n)))

/-- A continuous bounded interaction family has a continuous Dyson evolution on the compact
nonnegative interval where the uniform bound is available. -/
theorem continuousOn_evolution_of_bound {V : ℝ → A} {β M : ℝ}
    (h : ContinuousBoundedInteraction V β M) (lam : ℂ) :
    ContinuousOn (fun τ => evolution V lam τ) (Icc (0 : ℝ) β) := by
  apply (hasSumUniformlyOn_evolution_of_bound h.toBoundedInteraction lam).tendstoUniformlyOn.continuousOn
  exact (Filter.Eventually.of_forall fun s =>
    (continuous_finsetSum s fun n _ =>
      continuous_term h.interaction_continuous lam n).continuousOn).frequently

end
end Dyson

/-!
## First-variation bounds for generic Dyson evolution

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
    {V : ℝ → A} {β M : ℝ} (h : BoundedInteraction V β M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖evolution V lam τ - (1 + term V lam τ 1)‖ ≤
      ∑' n : ℕ, majorant (‖lam‖ * M) τ (n + 2) := by
  have htail :
      HasSum (fun n : ℕ => term V lam τ (n + 2))
        (evolution V lam τ - ∑ n ∈ Finset.range 2, term V lam τ n) :=
    (hasSum_nat_add_iff' 2).2
      (hasSum_evolution_of_bound h lam hτ)
  have hmajorant :
      Summable (fun n : ℕ => majorant (‖lam‖ * M) τ (n + 2)) :=
    (summable_nat_add_iff 2).2 (summable_majorant (‖lam‖ * M) τ)
  have hbound := htail.norm_le_of_bounded hmajorant.hasSum fun n =>
    norm_term_le_of_bound h lam (n + 2) hτ
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
    {V : ℝ → A} {β M : ℝ} (h : BoundedInteraction V β M)
    (lam : ℂ) (hlam : ‖lam‖ ≤ 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖evolution V lam τ - (1 + term V lam τ 1)‖ ≤
      ‖lam‖ ^ 2 * ∑' n : ℕ, majorant M τ (n + 2) := by
  refine (norm_evolution_sub_one_add_term_one_le_of_bound h lam hτ).trans ?_
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
          (norm_nonneg lam) hlam h.bound_nonneg hτ.1 n)
        hright
    _ = ‖lam‖ ^ 2 * ∑' n : ℕ, majorant M τ (n + 2) := by
      rw [tsum_mul_left]

/-- A Dyson evolution whose complex scalar coupling depends linearly on a real parameter is
differentiable at zero. The derivative is the exact first Dyson coefficient multiplied by the
linear coupling constant. -/
theorem hasDerivAt_evolution_linear_coupling_zero_of_bound
    {V : ℝ → A} {β M τ : ℝ} (h : BoundedInteraction V β M)
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
      h ((lam : ℂ) * κ) hlam' hτ
    have hscalar : lam • (-κ) = -((lam : ℂ) * κ) := by
      simpa [Algebra.smul_def] using (mul_neg (lam : ℂ) κ)
    have hlin :
        lam • ((-κ) • ∫ σ in (0 : ℝ)..τ, V σ) =
          term V ((lam : ℂ) * κ) τ 1 := by
      rw [term_one]
      calc
        lam • ((-κ) • ∫ σ in (0 : ℝ)..τ, V σ) =
            (lam • (-κ)) • ∫ σ in (0 : ℝ)..τ, V σ :=
          (IsScalarTower.smul_assoc lam (-κ)
            (∫ σ in (0 : ℝ)..τ, V σ)).symm
        _ = (-((lam : ℂ) * κ)) • ∫ σ in (0 : ℝ)..τ, V σ :=
          congrArg (fun z : ℂ => z • ∫ σ in (0 : ℝ)..τ, V σ) hscalar
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
  · simpa using habs.mul_const (‖κ‖ ^ 2 * C)

end
end Dyson

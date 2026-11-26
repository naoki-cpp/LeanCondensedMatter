import LeanCondensedMatter.Analysis.Dyson.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Volterra equation and uniqueness for bounded Dyson evolutions

This module exchanges the generic Dyson series with its Bochner interval integral and proves the
interaction-picture Volterra equation. The quantitative and continuity obligations are supplied
through the canonical bounded-interaction hypotheses on a compact nonnegative time interval.
Continuous solutions satisfy the right-derivative initial-value problem; a homogeneous Grönwall
estimate proves uniqueness on that interval.
-/

namespace Dyson

open Set

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A solution of the interaction-picture differential equation with unit initial value
satisfies the Volterra integral equation. This uses only the Banach-algebra structure and
continuity of the interaction; the endpoint can have either sign. -/
theorem eq_one_sub_integral_of_hasDerivAt {V U : ℝ → A}
    (hV : Continuous V) (lam : ℂ) (hzero : U 0 = 1)
    (hderiv : ∀ t : ℝ, HasDerivAt U (-(lam • (V t * U t))) t)
    (τ : ℝ) :
    U τ = 1 - lam • ∫ σ in (0 : ℝ)..τ, V σ * U σ := by
  have hU : Continuous U :=
    continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
  have hf : Continuous (fun σ : ℝ => -(lam • (V σ * U σ))) :=
    (continuous_const.smul (hV.mul hU)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun σ _ => hderiv σ) (hf.intervalIntegrable 0 τ)
  rw [hzero, intervalIntegral.integral_neg, intervalIntegral.integral_smul] at hFTC
  calc
    U τ = 1 + (U τ - 1) := by abel
    _ = 1 + (-(lam • ∫ σ in (0 : ℝ)..τ, V σ * U σ)) := by rw [← hFTC]
    _ = _ := by abel

/-- The `n`th term in the Volterra integrand, including the external coupling. -/
noncomputable def integrand (V : ℝ → A) (lam : ℂ) (n : ℕ) (σ : ℝ) : A :=
  lam • (V σ * term V lam σ n)

/-- A constant-in-time summable majorant for the Volterra integrand on `[0, β]`. -/
noncomputable def integrandMajorant (M β : ℝ) (lam : ℂ) (n : ℕ) : ℝ :=
  (‖lam‖ * M) * majorant (‖lam‖ * M) β n

/-- Every generic Volterra-integrand term is continuous for a continuous interaction family. -/
theorem continuous_integrand {V : ℝ → A} (hV : Continuous V) (lam : ℂ) (n : ℕ) :
    Continuous (integrand V lam n) := by
  change Continuous (fun σ => lam • (V σ * term V lam σ n))
  exact continuous_const.smul (hV.mul (continuous_term hV lam n))

/-- Left multiplication by the interaction and scalar multiplication carry the Dyson sum to the
pointwise Volterra integrand. -/
theorem hasSum_integrand_of_bound {V : ℝ → A} {β M σ : ℝ}
    (h : BoundedInteraction V β M)
    (hσ : σ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (fun n => integrand V lam n σ)
      (lam • (V σ * evolution V lam σ)) := by
  have hmul := (hasSum_evolution_of_bound h lam hσ).mul_left (V σ)
  simpa only [integrand] using hmul.const_smul lam

omit [CompleteSpace A] in
/-- Uniform pointwise norm control of every generic Volterra-integrand term on `[0, β]`. -/
theorem norm_integrand_le_of_bound {V : ℝ → A} {β M σ : ℝ}
    (h : BoundedInteraction V β M)
    (hσ : σ ∈ Icc (0 : ℝ) β) (lam : ℂ) (n : ℕ) :
    ‖integrand V lam n σ‖ ≤ integrandMajorant M β lam n := by
  have hweighted : 0 ≤ ‖lam‖ * M := mul_nonneg (norm_nonneg lam) h.bound_nonneg
  have hterm : ‖term V lam σ n‖ ≤ majorant (‖lam‖ * M) β n :=
    (norm_term_le_of_bound h lam n hσ).trans
      (majorant_mono_time hweighted hσ.1 hσ.2 n)
  calc
    ‖integrand V lam n σ‖ = ‖lam‖ * ‖V σ * term V lam σ n‖ := by
      rw [integrand, norm_smul]
    _ ≤ ‖lam‖ * (‖V σ‖ * ‖term V lam σ n‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg lam)
    _ ≤ ‖lam‖ * (M * majorant (‖lam‖ * M) β n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (h.interaction_norm_le σ hσ) hterm
          (norm_nonneg _) h.bound_nonneg)
        (norm_nonneg lam)
    _ = integrandMajorant M β lam n := by
      rw [integrandMajorant]
      ring

/-- The generic Volterra integrand series may be exchanged with the Bochner interval integral. -/
theorem hasSum_intervalIntegral_integrand_of_bound {V : ℝ → A} {β M τ : ℝ}
    (h : ContinuousBoundedInteraction V β M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum
      (fun n => ∫ σ in (0 : ℝ)..τ, integrand V lam n σ)
      (∫ σ in (0 : ℝ)..τ, lam • (V σ * evolution V lam σ)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => integrandMajorant M β lam n)
  · intro n
    exact (continuous_integrand h.interaction_continuous lam n).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun σ hσ => by
      have hσ' : σ ∈ Icc (0 : ℝ) τ := by
        simpa [uIcc_of_le hτ.1] using (uIoc_subset_uIcc hσ)
      exact norm_integrand_le_of_bound h.toBoundedInteraction
        ⟨hσ'.1, hσ'.2.trans hτ.2⟩ lam n
  · exact Filter.Eventually.of_forall fun _ _ =>
      (summable_majorant (‖lam‖ * M) β).mul_left (‖lam‖ * M)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun σ hσ => by
      have hσ' : σ ∈ Icc (0 : ℝ) τ := by
        simpa [uIcc_of_le hτ.1] using (uIoc_subset_uIcc hσ)
      exact hasSum_integrand_of_bound h.toBoundedInteraction
        ⟨hσ'.1, hσ'.2.trans hτ.2⟩ lam

omit [CompleteSpace A] in
/-- Integrating the `n`th generic Volterra term gives the negative `(n+1)`st Dyson term. -/
theorem intervalIntegral_integrand (V : ℝ → A) (τ : ℝ) (lam : ℂ) (n : ℕ) :
    (∫ σ in (0 : ℝ)..τ, integrand V lam n σ) = - term V lam τ (n + 1) := by
  rw [term, coeff_succ, smul_neg, neg_neg]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro σ _
  simp [integrand, term, pow_succ', smul_smul]

/-- The positive-order generic Dyson tail sums to the negative Volterra integral. -/
theorem hasSum_tail_of_bound {V : ℝ → A} {β M τ : ℝ}
    (h : ContinuousBoundedInteraction V β M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (fun n => term V lam τ (n + 1))
      (- ∫ σ in (0 : ℝ)..τ, lam • (V σ * evolution V lam σ)) := by
  simpa only [neg_neg] using
    (HasSum.congr_fun
      (hasSum_intervalIntegral_integrand_of_bound h hτ lam)
      (fun n => (intervalIntegral_integrand V τ lam n).symm)).neg

/-- The generic Dyson evolution solves the interaction-picture Volterra equation. -/
theorem evolution_eq_one_sub_integral_of_bound {V : ℝ → A} {β M τ : ℝ}
    (h : ContinuousBoundedInteraction V β M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    evolution V lam τ = 1 - lam • ∫ σ in (0 : ℝ)..τ, V σ * evolution V lam σ := by
  have hfull := hasSum_evolution_of_bound h.toBoundedInteraction lam hτ
  have hdecomp : HasSum (term V lam τ)
      (term V lam τ 0 +
        (- ∫ σ in (0 : ℝ)..τ, lam • (V σ * evolution V lam σ))) :=
    (hasSum_tail_of_bound h hτ lam).zero_add
  have heq := hfull.unique hdecomp
  simpa [term, sub_eq_add_neg, intervalIntegral.integral_smul] using heq

end
end Dyson

namespace Dyson

open Set Filter
open scoped Topology

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A continuous solution of the Volterra equation satisfies the corresponding right-derivative
initial-value problem on the half-open interval. -/
theorem hasDerivWithinAt_of_volterra {V U : ℝ → A} (hV : Continuous V)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτ : τ ∈ Ico (0 : ℝ) β) (lam : ℂ)
    (hU : ContinuousOn U (Icc (0 : ℝ) β))
    (hEq : ∀ u ∈ Icc (0 : ℝ) β,
      U u = 1 - lam • ∫ σ in (0 : ℝ)..u, V σ * U σ) :
    HasDerivWithinAt U (-(lam • (V τ * U τ))) (Ici τ) τ := by
  let g : ℝ → A := fun σ => V σ * U σ
  have hg : ContinuousOn g (Icc (0 : ℝ) β) := by
    exact hV.continuousOn.mul hU
  let p : ℝ → ℝ := fun x => (projIcc (0 : ℝ) β hβ x : ℝ)
  let gExt : ℝ → A := fun x => g (p x)
  have hp : Continuous p := by
    exact continuous_subtype_val.comp (LipschitzWith.projIcc hβ).continuous
  have hpmap : MapsTo p univ (Icc (0 : ℝ) β) := by
    intro x _
    exact (projIcc (0 : ℝ) β hβ x).property
  have hgExt : Continuous gExt := by
    apply continuousOn_univ.mp
    exact hg.comp hp.continuousOn hpmap
  have hgExt_eq : EqOn gExt g (Icc (0 : ℝ) β) := by
    intro x hx
    change g (p x) = g x
    rw [show p x = x by
      change ((projIcc (0 : ℝ) β hβ x : Icc (0 : ℝ) β) : ℝ) = x
      rw [projIcc_of_mem hβ hx]]
  have hτIcc : τ ∈ Icc (0 : ℝ) β := ⟨hτ.1, hτ.2.le⟩
  have hFTC0 : HasDerivWithinAt (fun u => ∫ σ in (0 : ℝ)..u, gExt σ)
      (gExt τ) (Ici τ) τ :=
    (hgExt.integral_hasStrictDerivAt (0 : ℝ) τ).hasDerivAt.hasDerivWithinAt
  have hFTC : HasDerivWithinAt (fun u => ∫ σ in (0 : ℝ)..u, gExt σ)
      (g τ) (Ici τ) τ :=
    hFTC0.congr_deriv (hgExt_eq hτIcc)
  let rhs : ℝ → A :=
    (fun _ => (1 : A)) - lam • (fun u => ∫ σ in (0 : ℝ)..u, gExt σ)
  have hrhs0 :=
    (hasDerivAt_const (x := τ) (c := (1 : A))).hasDerivWithinAt.sub
      (hFTC.const_smul lam)
  change HasDerivWithinAt rhs (0 - lam • g τ) (Ici τ) τ at hrhs0
  have hrhs : HasDerivWithinAt rhs (-(lam • g τ)) (Ici τ) τ :=
    hrhs0.congr_deriv (by simp)
  have hIcc_mem : Icc (0 : ℝ) β ∈ 𝓝[Ici τ] τ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio β, Iio_mem_nhds hτ.2, ?_⟩
    rintro x ⟨hxβ, hτx⟩
    exact ⟨hτ.1.trans hτx, le_of_lt hxβ⟩
  have heq : U =ᶠ[𝓝[Ici τ] τ] rhs := by
    filter_upwards [hIcc_mem] with u hu
    have huIcc : uIcc (0 : ℝ) u ⊆ Icc (0 : ℝ) β := by
      rw [uIcc_of_le hu.1]
      exact Icc_subset_Icc_right hu.2
    have hintEq :
        (∫ σ in (0 : ℝ)..u, gExt σ) = ∫ σ in (0 : ℝ)..u, g σ := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      exact hgExt_eq (huIcc hσ)
    rw [show rhs u = (1 : A) - lam • ∫ σ in (0 : ℝ)..u, gExt σ by rfl, hintEq]
    simpa only [g] using hEq u hu
  have hpoint : U τ = rhs τ := by
    have hτuIcc : uIcc (0 : ℝ) τ ⊆ Icc (0 : ℝ) β := by
      rw [uIcc_of_le hτ.1]
      exact Icc_subset_Icc_right hτ.2.le
    have hintEq :
        (∫ σ in (0 : ℝ)..τ, gExt σ) = ∫ σ in (0 : ℝ)..τ, g σ := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      exact hgExt_eq (hτuIcc hσ)
    rw [show rhs τ = (1 : A) - lam • ∫ σ in (0 : ℝ)..τ, gExt σ by rfl, hintEq]
    simpa only [g] using hEq τ hτIcc
  exact hrhs.congr_of_eventuallyEq heq hpoint

/-- Two continuous solutions of the same bounded Dyson–Volterra equation agree on `[0, β]`. -/
theorem eqOn_of_volterra_of_bound {V U W : ℝ → A} (hVcont : Continuous V)
    {β M : ℝ} (hβ : 0 ≤ β)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M) (lam : ℂ)
    (hU : ContinuousOn U (Icc (0 : ℝ) β))
    (hW : ContinuousOn W (Icc (0 : ℝ) β))
    (hUEq : ∀ t ∈ Icc (0 : ℝ) β,
      U t = 1 - lam • ∫ σ in (0 : ℝ)..t, V σ * U σ)
    (hWEq : ∀ t ∈ Icc (0 : ℝ) β,
      W t = 1 - lam • ∫ σ in (0 : ℝ)..t, V σ * W σ) :
    EqOn U W (Icc (0 : ℝ) β) := by
  let d : ℝ → A := fun t => U t - W t
  let d' : ℝ → A := fun t =>
    -(lam • (V t * U t)) - (-(lam • (V t * W t)))
  have hd : ContinuousOn d (Icc (0 : ℝ) β) := hU.sub hW
  have hd' : ∀ t ∈ Ico (0 : ℝ) β,
      HasDerivWithinAt d (d' t) (Ici t) t := by
    intro t ht
    exact (hasDerivWithinAt_of_volterra hVcont hβ ht lam hU hUEq).sub
      (hasDerivWithinAt_of_volterra hVcont hβ ht lam hW hWEq)
  have hd0 : d 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) β := ⟨le_rfl, hβ⟩
    rw [show d 0 = U 0 - W 0 by rfl, hUEq 0 h0, hWEq 0 h0]
    simp
  have hbound : ∀ t ∈ Ico (0 : ℝ) β, ‖d' t‖ ≤ (‖lam‖ * M) * ‖d t‖ := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) β := ⟨ht.1, ht.2.le⟩
    have hd'eq : d' t = -(lam • (V t * d t)) := by
      simp only [d', d, mul_sub, smul_sub]
      abel
    rw [hd'eq, norm_neg, norm_smul]
    calc
      ‖lam‖ * ‖V t * d t‖ ≤ ‖lam‖ * (‖V t‖ * ‖d t‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg lam)
      _ ≤ ‖lam‖ * (M * ‖d t‖) := by
        gcongr
        exact hV t htIcc
      _ = (‖lam‖ * M) * ‖d t‖ := by ring
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := d) (f' := d') (K := ‖lam‖ * M) (a := (0 : ℝ)) (b := β)
    hd hd' hd0 hbound
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

/-- The generic Dyson evolution is the unique continuous solution of its bounded Volterra equation
on `[0, β]`. -/
theorem eqOn_evolution_of_volterra_of_bound {V U : ℝ → A}
    {β M : ℝ} (hβ : 0 ≤ β) (h : ContinuousBoundedInteraction V β M) (lam : ℂ)
    (hU : ContinuousOn U (Icc (0 : ℝ) β))
    (hUEq : ∀ t ∈ Icc (0 : ℝ) β,
      U t = 1 - lam • ∫ σ in (0 : ℝ)..t, V σ * U σ) :
    EqOn U (fun t => evolution V lam t) (Icc (0 : ℝ) β) := by
  apply eqOn_of_volterra_of_bound h.interaction_continuous hβ
    h.toBoundedInteraction.interaction_norm_le lam hU
    (continuousOn_evolution_of_bound h lam) hUEq
  intro t ht
  exact evolution_eq_one_sub_integral_of_bound h ht lam

end
end Dyson

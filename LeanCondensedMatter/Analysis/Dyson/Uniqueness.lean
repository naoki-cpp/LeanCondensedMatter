import LeanCondensedMatter.Analysis.Dyson.Volterra
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Uniqueness for bounded Dyson–Volterra solutions

A continuous solution of the bounded Volterra equation has the expected right derivative.  The
difference of two solutions therefore satisfies a homogeneous Grönwall estimate and vanishes on
the compact nonnegative interval.
-/

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
theorem eqOn_evolution_of_volterra_of_bound {V U : ℝ → A} (hVcont : Continuous V)
    {β M : ℝ} (hβ : 0 ≤ β) (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M) (lam : ℂ)
    (hU : ContinuousOn U (Icc (0 : ℝ) β))
    (hUEq : ∀ t ∈ Icc (0 : ℝ) β,
      U t = 1 - lam • ∫ σ in (0 : ℝ)..t, V σ * U σ) :
    EqOn U (fun t => evolution V lam t) (Icc (0 : ℝ) β) := by
  apply eqOn_of_volterra_of_bound hVcont hβ hV lam hU
    (continuousOn_evolution_of_bound hVcont hOne hM hV lam) hUEq
  intro t ht
  exact evolution_eq_one_sub_integral_of_bound hVcont hOne hM hV ht lam

end
end Dyson

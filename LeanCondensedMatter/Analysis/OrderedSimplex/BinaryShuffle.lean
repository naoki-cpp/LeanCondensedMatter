import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.Combinatorics.BinaryShuffle

set_option linter.style.header false

/-!
# Explicit binary-shuffle ordered-simplex contributions

Each `BinaryShuffle m n` recursively specifies whether the current outermost time belongs to the
left or right factor. This module turns that combinatorial datum into one iterated integral, proves
joint continuity in external parameters, and records the all-left and all-right boundary identities.
-/

namespace Combinatorics
namespace BinaryShuffle

open intervalIntegral

private theorem continuous_uncurry_finCons {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {f : X → (Fin (n + 1) → ℝ) → Y}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry
      (fun y : X × ℝ => fun rest : Fin n → ℝ => f y.1 (Fin.cons y.2 rest))) := by
  have hcons : Continuous
      (fun z : (X × ℝ) × (Fin n → ℝ) =>
        (Fin.cons z.1.2 z.2 : Fin (n + 1) → ℝ)) :=
    Continuous.finCons (continuous_snd.comp continuous_fst) continuous_snd
  exact hf.comp ((continuous_fst.comp continuous_fst).prodMk hcons)

private theorem continuous_uncurry_fst {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {f : X → (Fin n → ℝ) → Y}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry
      (fun y : X × ℝ => fun times : Fin n → ℝ => f y.1 times)) := by
  exact hf.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)

/-- The ordered-simplex contribution of one explicit binary shuffle. -/
noncomputable def orderedSimplexContribution :
    {m n : ℕ} → BinaryShuffle m n → ℝ →
      ((Fin m → ℝ) → ℂ) → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, 0, .nil, _β, f, g => f Fin.elim0 * g Fin.elim0
  | _m + 1, _n, .consLeft σ, β, f, g =>
      ∫ t in (0 : ℝ)..β,
        orderedSimplexContribution σ t (fun rest => f (Fin.cons t rest)) g
  | _m, _n + 1, .consRight σ, β, f, g =>
      ∫ t in (0 : ℝ)..β,
        orderedSimplexContribution σ t f (fun rest => g (Fin.cons t rest))

/-- Joint continuity of one shuffle contribution through a varying upper bound and two
parameter-dependent integrands. -/
theorem continuous_orderedSimplexContribution_of_continuous {X : Type*} [TopologicalSpace X] :
    ∀ {m n : ℕ} (σ : BinaryShuffle m n) (bound : X → ℝ)
      (f : X → (Fin m → ℝ) → ℂ) (g : X → (Fin n → ℝ) → ℂ),
      Continuous bound → Continuous (Function.uncurry f) → Continuous (Function.uncurry g) →
      Continuous (fun x => orderedSimplexContribution σ (bound x) (f x) (g x))
  | 0, 0, .nil, bound, f, g, _hbound, hf, hg => by
      have hf0 : Continuous (fun x => f x Fin.elim0) :=
        hf.comp (continuous_id.prodMk continuous_const)
      have hg0 : Continuous (fun x => g x Fin.elim0) :=
        hg.comp (continuous_id.prodMk continuous_const)
      change Continuous ((fun x => f x Fin.elim0) * fun x => g x Fin.elim0)
      exact hf0.mul hg0
  | m + 1, n, .consLeft σ, bound, f, g, hbound, hf, hg => by
      have hf' : Continuous (Function.uncurry
          (fun y : X × ℝ => fun rest : Fin m → ℝ => f y.1 (Fin.cons y.2 rest))) :=
        continuous_uncurry_finCons hf
      have hg' : Continuous (Function.uncurry
          (fun y : X × ℝ => fun times : Fin n → ℝ => g y.1 times)) :=
        continuous_uncurry_fst hg
      have hinner := continuous_orderedSimplexContribution_of_continuous σ Prod.snd
        (fun y : X × ℝ => fun rest => f y.1 (Fin.cons y.2 rest))
        (fun y : X × ℝ => g y.1) continuous_snd hf' hg'
      simpa [orderedSimplexContribution] using
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hinner hbound
  | m, n + 1, .consRight σ, bound, f, g, hbound, hf, hg => by
      have hf' : Continuous (Function.uncurry
          (fun y : X × ℝ => fun times : Fin m → ℝ => f y.1 times)) :=
        continuous_uncurry_fst hf
      have hg' : Continuous (Function.uncurry
          (fun y : X × ℝ => fun rest : Fin n → ℝ => g y.1 (Fin.cons y.2 rest))) :=
        continuous_uncurry_finCons hg
      have hinner := continuous_orderedSimplexContribution_of_continuous σ Prod.snd
        (fun y : X × ℝ => f y.1)
        (fun y : X × ℝ => fun rest => g y.1 (Fin.cons y.2 rest))
        continuous_snd hf' hg'
      simpa [orderedSimplexContribution] using
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hinner hbound

/-- The unique all-right shuffle contributes the right ordered-simplex integral times the
zero-dimensional left value. -/
theorem orderedSimplexContribution_allRight :
    ∀ (n : ℕ) (β : ℝ) (f : (Fin 0 → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ),
      orderedSimplexContribution (allRight n) β f g =
        f Fin.elim0 * orderedSimplexIntegral n β g
  | 0, β, f, g => by
      rfl
  | n + 1, β, f, g => by
      rw [allRight, orderedSimplexContribution, orderedSimplexIntegral_succ]
      simp_rw [orderedSimplexContribution_allRight n]
      rw [intervalIntegral.integral_const_mul]

/-- The unique all-left shuffle contributes the left ordered-simplex integral times the
zero-dimensional right value. -/
theorem orderedSimplexContribution_allLeft :
    ∀ (m : ℕ) (β : ℝ) (f : (Fin m → ℝ) → ℂ) (g : (Fin 0 → ℝ) → ℂ),
      orderedSimplexContribution (allLeft m) β f g =
        orderedSimplexIntegral m β f * g Fin.elim0
  | 0, β, f, g => by
      rfl
  | m + 1, β, f, g => by
      rw [allLeft, orderedSimplexContribution, orderedSimplexIntegral_succ]
      simp_rw [orderedSimplexContribution_allLeft m]
      rw [intervalIntegral.integral_mul_const]

end BinaryShuffle
end Combinatorics

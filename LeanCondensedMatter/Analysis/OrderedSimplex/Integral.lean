import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-!
# Ordered-simplex iterated scalar integrals

This module defines a `ℂ`-valued iterated integral recursively through `intervalIntegral`. For
`0 ≤ β`, it is the iterated integral over the ordered simplex
`0 ≤ τₙ₋₁ ≤ ⋯ ≤ τ₁ ≤ τ₀ ≤ β`. For arbitrary real `β`, including negative values,
`intervalIntegral` supplies the corresponding recursively oriented extension rather than an integral
over that simplex as a subset of `ℝⁿ`. In particular, `orderedSimplexIntegral_const` gives `βⁿ/n!`
for every real `β`, which is a simplex volume only when `0 ≤ β`.

Coordinate `0` is the latest and outermost time: the recursion integrates it over `[0, β]` and then
recurses on the remaining coordinates with the current outer time as their bound. The module also
provides joint continuity when both the bound and integrand vary continuously, and finite-sum
linearity under an explicit continuity hypothesis on each summand.
-/

namespace intervalIntegral

/-- The iterated integral over the ordered simplex `0 ≤ τₙ₋₁ ≤ ⋯ ≤ τ₁ ≤ τ₀ ≤ β` for `0 ≤ β`
(vacuously `f Fin.elim0` at `n = 0`, the empty simplex); for arbitrary `β : ℝ`, the corresponding
recursively oriented interval-integral extension. Coordinate `0` is the latest/outermost time: the
recursion integrates the outermost coordinate `τ` over `[0, β]`, then recurses into the remaining
`n` coordinates over `[0, τ]`. -/
noncomputable def orderedSimplexIntegral :
    (n : ℕ) → ℝ → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, _β, f => f Fin.elim0
  | n + 1, β, f =>
      ∫ τ in (0 : ℝ)..β, orderedSimplexIntegral n τ (fun rest => f (Fin.cons τ rest))

@[simp]
theorem orderedSimplexIntegral_zero (β : ℝ) (f : (Fin 0 → ℝ) → ℂ) :
    orderedSimplexIntegral 0 β f = f Fin.elim0 := rfl

theorem orderedSimplexIntegral_succ (n : ℕ) (β : ℝ) (f : (Fin (n + 1) → ℝ) → ℂ) :
    orderedSimplexIntegral (n + 1) β f =
      ∫ τ in (0 : ℝ)..β, orderedSimplexIntegral n τ (fun rest => f (Fin.cons τ rest)) := rfl

theorem orderedSimplexIntegral_congr {n : ℕ} {β : ℝ} {f g : (Fin n → ℝ) → ℂ}
    (h : ∀ τ, f τ = g τ) : orderedSimplexIntegral n β f = orderedSimplexIntegral n β g := by
  induction n generalizing β with
  | zero => simp [h]
  | succ n ih =>
    rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
    exact intervalIntegral.integral_congr fun τ _ => ih fun rest => h (Fin.cons τ rest)

/-- Changing the presentation of the finite coordinate count only precomposes the integrand with the
corresponding `Fin.cast`. -/
theorem orderedSimplexIntegral_cast {a b : ℕ} (h : a = b) (β : ℝ)
    (F : (Fin a → ℝ) → ℂ) :
    orderedSimplexIntegral a β F =
      orderedSimplexIntegral b β (fun τ => F (fun i => τ (Fin.cast h i))) := by
  subst b
  rfl

@[simp]
theorem orderedSimplexIntegral_zero_fun (n : ℕ) (β : ℝ) :
    orderedSimplexIntegral n β (fun _ => (0 : ℂ)) = 0 := by
  induction n generalizing β with
  | zero => rfl
  | succ n ih => simp [orderedSimplexIntegral_succ, ih]

theorem orderedSimplexIntegral_smul (n : ℕ) (β : ℝ) (c : ℂ) (f : (Fin n → ℝ) → ℂ) :
    orderedSimplexIntegral n β (fun τ => c * f τ) = c * orderedSimplexIntegral n β f := by
  induction n generalizing β with
  | zero => rfl
  | succ n ih =>
    rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
    simp_rw [ih]
    rw [intervalIntegral.integral_const_mul]

theorem orderedSimplexIntegral_neg (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → ℂ) :
    orderedSimplexIntegral n β (fun τ => -f τ) = -orderedSimplexIntegral n β f := by
  have h := orderedSimplexIntegral_smul n β (-1) f
  simpa using h

/-- On a constant function, the ordered-simplex integral is `βⁿ/n!` times the constant. -/
theorem orderedSimplexIntegral_const (n : ℕ) (β : ℝ) (c : ℂ) :
    orderedSimplexIntegral n β (fun _ => c) = (β ^ n / n.factorial : ℝ) * c := by
  induction n generalizing β with
  | zero => simp
  | succ n ih =>
    rw [orderedSimplexIntegral_succ]
    simp_rw [ih]
    rw [show (fun τ : ℝ => (τ ^ n / n.factorial : ℝ) * c) =
        fun τ : ℝ => ((τ ^ n / n.factorial : ℝ) : ℂ) * c from rfl,
      intervalIntegral.integral_mul_const]
    rw [show (∫ τ in (0:ℝ)..β, ((τ ^ n / n.factorial : ℝ) : ℂ)) =
        ((∫ τ in (0:ℝ)..β, τ ^ n / n.factorial : ℝ) : ℂ) from by
      rw [← intervalIntegral.integral_ofReal]]
    rw [intervalIntegral.integral_div, integral_pow]
    have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hne1 : ((n : ℂ) + 1) ≠ 0 := by
      simp [Nat.cast_add_one_ne_zero]
    push_cast
    rw [hfac]
    field_simp
    ring

/-- If the upper bound and integrand vary continuously with a parameter `x`, then
`x ↦ orderedSimplexIntegral n (bound x) (f x)` is continuous. -/
theorem continuous_orderedSimplexIntegral_of_continuous {X : Type*} [TopologicalSpace X] :
    ∀ (n : ℕ) (bound : X → ℝ) (f : X → (Fin n → ℝ) → ℂ), Continuous bound →
      Continuous (Function.uncurry f) →
      Continuous (fun x => orderedSimplexIntegral n (bound x) (f x))
  | 0, bound, f, _, hf => by
    simp only [orderedSimplexIntegral_zero]
    exact hf.comp (continuous_id.prodMk continuous_const)
  | n + 1, bound, f, hbound, hf => by
    simp_rw [orderedSimplexIntegral_succ]
    have hf' : Continuous (Function.uncurry
        (fun (y : X × ℝ) (rest : Fin n → ℝ) => f y.1 (Fin.cons y.2 rest))) := by
      have hcons : Continuous
          (fun z : (X × ℝ) × (Fin n → ℝ) => Fin.cons z.1.2 z.2 : (X × ℝ) × (Fin n → ℝ) →
            Fin (n + 1) → ℝ) :=
        Continuous.finCons (continuous_snd.comp continuous_fst) continuous_snd
      exact hf.comp ((continuous_fst.comp continuous_fst).prodMk hcons)
    have hF := continuous_orderedSimplexIntegral_of_continuous n Prod.snd
      (fun (y : X × ℝ) (rest : Fin n → ℝ) => f y.1 (Fin.cons y.2 rest)) continuous_snd hf'
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hbound

/-- A finite sum commutes with `orderedSimplexIntegral` when every summand is continuous. -/
theorem orderedSimplexIntegral_finsetSum {ι : Type*} (s : Finset ι) (n : ℕ) (β : ℝ)
    (f : ι → (Fin n → ℝ) → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) :
    orderedSimplexIntegral n β (fun τ => ∑ i ∈ s, f i τ) =
      ∑ i ∈ s, orderedSimplexIntegral n β (f i) := by
  induction n generalizing β with
  | zero => simp
  | succ n ih =>
    have hcons : ∀ i ∈ s, Continuous (fun p : ℝ × (Fin n → ℝ) => f i (Fin.cons p.1 p.2)) :=
      fun i hi => (hf i hi).comp (Continuous.finCons continuous_fst continuous_snd)
    have heq : ∀ τ : ℝ, orderedSimplexIntegral n τ (fun rest => ∑ i ∈ s, f i (Fin.cons τ rest)) =
        ∑ i ∈ s, orderedSimplexIntegral n τ (fun rest => f i (Fin.cons τ rest)) := fun τ =>
      ih τ (fun i rest => f i (Fin.cons τ rest))
        (fun i hi => (hcons i hi).comp (continuous_const.prodMk continuous_id))
    rw [orderedSimplexIntegral_succ]
    simp_rw [heq]
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => (orderedSimplexIntegral_succ n β (f i)).symm
    · intro i hi
      exact (continuous_orderedSimplexIntegral_of_continuous n id
        (fun τ rest => f i (Fin.cons τ rest)) continuous_id (hcons i hi)).intervalIntegrable 0 β

end intervalIntegral

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

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
provides joint continuity and joint measurability when the bound and integrand vary with a
parameter, endpoint differentiation for continuous integrands, and finite-sum linearity under an
explicit continuity hypothesis on each summand.
-/

namespace intervalIntegral

open MeasureTheory

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

/-- Fundamental theorem of calculus for an ordered-simplex integral: differentiating in the upper
bound fixes the outermost time coordinate at that bound. -/
theorem hasDerivAt_orderedSimplexIntegral_succ (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (hf : Continuous f) (β : ℝ) :
    HasDerivAt (fun t : ℝ => orderedSimplexIntegral (n + 1) t f)
      (orderedSimplexIntegral n β (fun rest => f (Fin.cons β rest))) β := by
  have hboundary : Continuous (fun t : ℝ =>
      orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))) :=
    continuous_orderedSimplexIntegral_of_continuous n id
      (fun t rest => f (Fin.cons t rest)) continuous_id
      (hf.comp (Continuous.finCons continuous_fst continuous_snd))
  simpa only [orderedSimplexIntegral_succ] using
    (hboundary.integral_hasStrictDerivAt 0 β).hasDerivAt

/-- A jointly measurable integrand remains measurable after integration from `0` to a measurable
parameter-dependent upper bound. -/
private theorem measurable_parametric_intervalIntegral_zero
    {X : Type*} [MeasurableSpace X]
    (bound : X → ℝ) (F : X → ℝ → ℂ)
    (hbound : Measurable bound) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => ∫ t in (0 : ℝ)..bound x, F x t) := by
  let left : X → ℝ → ℂ := fun x t =>
    if t ∈ Set.Ioc (0 : ℝ) (bound x) then F x t else 0
  let right : X → ℝ → ℂ := fun x t =>
    if t ∈ Set.Ioc (bound x) (0 : ℝ) then F x t else 0
  have hleftSet : MeasurableSet
      {p : X × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) (bound p.1)} := by
    simp only [Set.mem_Ioc]
    measurability
  have hrightSet : MeasurableSet
      {p : X × ℝ | p.2 ∈ Set.Ioc (bound p.1) (0 : ℝ)} := by
    simp only [Set.mem_Ioc]
    measurability
  have hleft : StronglyMeasurable (Function.uncurry left) := by
    exact (hF.ite hleftSet measurable_const).stronglyMeasurable
  have hright : StronglyMeasurable (Function.uncurry right) := by
    exact (hF.ite hrightSet measurable_const).stronglyMeasurable
  have hleftInt := hleft.integral_prod_right (ν := volume)
  have hrightInt := hright.integral_prod_right (ν := volume)
  have hsub := hleftInt.sub hrightInt
  have heq : (fun x => ∫ t in (0 : ℝ)..bound x, F x t) =
      fun x => (∫ t, left x t) - ∫ t, right x t := by
    funext x
    rw [intervalIntegral]
    apply congrArg₂ (· - ·)
    · rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by simp [left, Set.indicator]
    · rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by simp [right, Set.indicator]
  rw [heq]
  exact hsub.measurable

/-- Measurable analogue of `continuous_orderedSimplexIntegral_of_continuous`. -/
theorem measurable_orderedSimplexIntegral_of_measurable {X : Type*} [MeasurableSpace X] :
    ∀ (n : ℕ) (bound : X → ℝ) (f : X → (Fin n → ℝ) → ℂ),
      Measurable bound → Measurable (Function.uncurry f) →
      Measurable (fun x => orderedSimplexIntegral n (bound x) (f x))
  | 0, _bound, f, _hbound, hf => by
      have hpair : Measurable
          (fun x : X => (x, (Fin.elim0 : Fin 0 → ℝ))) := by
        measurability
      change Measurable
        (fun x : X => Function.uncurry f (x, (Fin.elim0 : Fin 0 → ℝ)))
      exact hf.comp hpair
  | n + 1, bound, f, hbound, hf => by
      simp_rw [orderedSimplexIntegral_succ]
      have hf' : Measurable (Function.uncurry
          (fun y : X × ℝ => fun rest : Fin n → ℝ => f y.1 (Fin.cons y.2 rest))) := by
        have hmap : Measurable
            (fun z : (X × ℝ) × (Fin n → ℝ) =>
              (z.1.1, (Fin.cons z.1.2 z.2 : Fin (n + 1) → ℝ))) := by
          measurability
        exact hf.comp hmap
      have hinner := measurable_orderedSimplexIntegral_of_measurable n Prod.snd
        (fun y : X × ℝ => fun rest => f y.1 (Fin.cons y.2 rest)) measurable_snd hf'
      exact measurable_parametric_intervalIntegral_zero bound
        (fun x t => orderedSimplexIntegral n t (fun rest => f x (Fin.cons t rest)))
        hbound hinner

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

/-!
# Ordered-simplex integrals only see strictly decreasing time assignments

`orderedSimplexIntegral` is an iterated interval integral, each level ranging over `(0, τ i)`. Its
integrand is therefore only ever evaluated at strictly decreasing assignments, apart from one
endpoint per level, which a one-dimensional interval integral does not see.

So two integrands agreeing on strictly decreasing assignments have equal ordered-simplex integrals.
No measure theory on `Fin n → ℝ` is involved: the coincidence locus is not a positive-codimension
subset to be shown null, it is a single point of each nested interval.

This is what lets the two-point linked-cluster development use relabel covariance, which holds only
at injective interaction-time assignments — and a strictly decreasing assignment is injective.
-/

namespace intervalIntegral

open MeasureTheory

/-- Prepending a value above a strictly decreasing family keeps it strictly decreasing. -/
private theorem strictAnti_cons {m : ℕ} {τ₀ : ℝ} {rest : Fin m → ℝ}
    (hrest : StrictAnti rest) (hb : ∀ i, rest i < τ₀) : StrictAnti (Fin.cons τ₀ rest) := by
  intro a b hab
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
  · exact absurd hab (lt_irrefl _)
  · simpa using hb j
  · exact absurd hab (Fin.not_lt_zero _)
  · simp only [Fin.cons_succ]
    exact hrest (Fin.succ_lt_succ_iff.mp hab)

/-- **Only strictly decreasing assignments matter.** Two integrands that agree on every strictly
decreasing assignment bounded by `β` have the same ordered-simplex integral. -/
theorem orderedSimplexIntegral_congr_of_strictAnti :
    ∀ (n : ℕ) (β : ℝ), 0 ≤ β → ∀ f g : (Fin n → ℝ) → ℂ,
      (∀ τ : Fin n → ℝ, StrictAnti τ → (∀ i, τ i < β) → f τ = g τ) →
        orderedSimplexIntegral n β f = orderedSimplexIntegral n β g := by
  intro n
  induction n with
  | zero =>
      intro β _ f g h
      exact h Fin.elim0 (fun a _ _ => a.elim0) (fun i => i.elim0)
  | succ m ih =>
      intro β hβ f g h
      rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
      have hne : ∀ᵐ τ₀ : ℝ, τ₀ ≠ β := by
        rw [MeasureTheory.ae_iff]
        simp
      refine integral_congr_ae ?_
      filter_upwards [hne] with τ₀ hτ₀ hmem
      have hmem' : 0 < τ₀ ∧ τ₀ ≤ β := by
        rw [Set.uIoc_of_le hβ] at hmem
        exact ⟨hmem.1, hmem.2⟩
      have hlt : τ₀ < β := lt_of_le_of_ne hmem'.2 hτ₀
      refine ih τ₀ (le_of_lt hmem'.1) _ _ fun rest hanti hbound => ?_
      refine h (Fin.cons τ₀ rest) (strictAnti_cons hanti hbound) fun i => ?_
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simpa using hlt
      · simpa using lt_trans (hbound j) hlt

end intervalIntegral

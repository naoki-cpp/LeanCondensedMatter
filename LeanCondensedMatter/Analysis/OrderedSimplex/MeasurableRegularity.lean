import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact

set_option linter.style.header false

/-!
# Measurable bounded regularity for ordered-simplex integrands

The shuffle theorem only needs enough regularity to make every recursively exposed boundary
integrand interval integrable.  Global continuity is stronger than necessary.  This file packages a
weaker condition suited to finite chamber selections: global measurability together with uniform
boundedness on every centered finite-dimensional cube.

The condition is stable under fixing the outermost coordinate.  We also prove the measurable
analogue of `continuous_orderedSimplexIntegral_of_continuous`: a jointly measurable parametrized
integrand with a measurable upper bound has a measurable recursively oriented ordered-simplex
integral.
-/

namespace intervalIntegral

open MeasureTheory Set

private theorem exists_norm_bound_on_compact_of_finite_continuous_selection
    {ι X E : Type*} [Finite ι] [TopologicalSpace X] [SeminormedAddGroup E]
    (K : Set X) (hK : IsCompact K) (f : X → E) (g : ι → X → E)
    (hg : ∀ i, Continuous (g i))
    (hselect : ∀ x ∈ K, ∃ i, f x = g i x) :
    ∃ C : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C := by
  classical
  letI := Fintype.ofFinite ι
  let envelope : X → ℝ := fun x => ∑ i : ι, ‖g i x‖
  have hEnvelope : Continuous envelope := by
    dsimp [envelope]
    exact continuous_finsetSum _ fun i _ => (hg i).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hEnvelope.continuousOn
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hselect x hx
  have hterm : ‖f x‖ ≤ envelope x := by
    rw [hi]
    dsimp [envelope]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (g j x)) (Finset.mem_univ i)
  have hnonneg : 0 ≤ envelope x := by
    dsimp [envelope]
    exact Finset.sum_nonneg fun j _ => norm_nonneg (g j x)
  have hbound := hC x hx
  have hEnvelopeLe : envelope x ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound
  exact hterm.trans hEnvelopeLe

/-- The centered coordinate cube of radius `R`.  It is used instead of `[0, β]^n` so that fixing a
coordinate preserves local boundedness even when later bounds have the opposite sign. -/
def orderedSimplexTimeCube (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ => -R) (fun _ => R)

/-- A measurable function that is uniformly bounded on every centered coordinate cube. -/
def MeasurableLocallyBounded {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  Measurable f ∧
    ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ orderedSimplexTimeCube n R, ‖f x‖ ≤ C

/-- A globally measurable finite selection from continuous branches is measurably locally bounded. -/
theorem measurableLocallyBounded_of_finite_continuous_selection
    {ι : Type*} [Finite ι] {n : ℕ}
    (f : (Fin n → ℝ) → ℂ) (g : ι → (Fin n → ℝ) → ℂ)
    (hf : Measurable f) (hg : ∀ i, Continuous (g i))
    (hselect : ∀ x, ∃ i, f x = g i x) :
    MeasurableLocallyBounded f := by
  refine ⟨hf, ?_⟩
  intro R _hR
  obtain ⟨C, hC⟩ :=
    exists_norm_bound_on_compact_of_finite_continuous_selection
      (orderedSimplexTimeCube n R)
      (by
        simpa [orderedSimplexTimeCube] using
          (isCompact_Icc : IsCompact
            (Set.Icc (fun _ : Fin n => -R) (fun _ : Fin n => R))))
      f g hg (fun x _ => hselect x)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

/-- Every continuous finite-dimensional ordered-simplex integrand is measurably locally bounded. -/
theorem Continuous.measurableLocallyBounded {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) : MeasurableLocallyBounded f :=
  measurableLocallyBounded_of_finite_continuous_selection
    f (fun _ : Unit => f) hf.measurable (fun _ => hf) (fun _ => ⟨(), rfl⟩)

/-- Constants are measurably locally bounded. -/
theorem measurableLocallyBounded_const {n : ℕ} (c : ℂ) :
    MeasurableLocallyBounded (fun _ : Fin n → ℝ => c) :=
  ⟨measurable_const, fun _ _ => ⟨‖c‖, norm_nonneg c, fun _ _ => le_rfl⟩⟩

/-- Measurable local boundedness is preserved by pointwise multiplication: the product of two
uniform cube bounds bounds the product. -/
theorem MeasurableLocallyBounded.mul {n : ℕ} {f g : (Fin n → ℝ) → ℂ}
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    MeasurableLocallyBounded (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  intro R hR
  obtain ⟨C, hC0, hC⟩ := hf.2 R hR
  obtain ⟨D, hD0, hD⟩ := hg.2 R hR
  refine ⟨C * D, mul_nonneg hC0 hD0, ?_⟩
  intro x hx
  calc
    ‖f x * g x‖ = ‖f x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ C * D := mul_le_mul (hC x hx) (hD x hx) (norm_nonneg _) hC0

/-- A finite product of measurably locally bounded integrands is measurably locally bounded. -/
theorem MeasurableLocallyBounded.finsetProd {ι : Type*} {n : ℕ} (s : Finset ι)
    (f : ι → (Fin n → ℝ) → ℂ) (hf : ∀ i ∈ s, MeasurableLocallyBounded (f i)) :
    MeasurableLocallyBounded (fun x => ∏ i ∈ s, f i x) := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction f MeasurableLocallyBounded
    (fun _ _ ha hb => ha.mul hb) (measurableLocallyBounded_const (n := n) 1) hf

/-- Fixing the outermost finite coordinate preserves measurable local boundedness. -/
theorem MeasurableLocallyBounded.finCons {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℂ} (hf : MeasurableLocallyBounded f) (t : ℝ) :
    MeasurableLocallyBounded (fun rest : Fin n → ℝ => f (Fin.cons t rest)) := by
  refine ⟨hf.1.comp (Continuous.finCons continuous_const continuous_id).measurable, ?_⟩
  intro R hR
  let R' := max R |t|
  have hR' : 0 ≤ R' := le_trans hR (le_max_left _ _)
  obtain ⟨C, hC0, hC⟩ := hf.2 R' hR'
  refine ⟨C, hC0, ?_⟩
  intro rest hrest
  apply hC
  rw [orderedSimplexTimeCube, Set.mem_Icc] at hrest ⊢
  constructor
  · intro i
    induction i using Fin.cases with
    | zero =>
        have ht : |t| ≤ R' := le_max_right _ _
        exact (neg_le_neg ht).trans (neg_abs_le t)
    | succ i =>
        exact (neg_le_neg (le_max_left R |t|)).trans (hrest.1 i)
  · intro i
    induction i using Fin.cases with
    | zero =>
        have ht : |t| ≤ R' := le_max_right _ _
        exact (le_abs_self t).trans ht
    | succ i =>
        exact (hrest.2 i).trans (le_max_left R |t|)

/-- A jointly measurable integrand remains measurable after integration from `0` to a measurable
parameter-dependent upper bound. -/
theorem measurable_parametric_intervalIntegral_zero
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

/-- For a measurable integrand, its ordered-simplex integral is measurable as a function of the
recursively oriented upper bound. -/
theorem measurable_orderedSimplexIntegral_bound {n : ℕ}
    (f : (Fin n → ℝ) → ℂ) (hf : Measurable f) :
    Measurable (fun β : ℝ => orderedSimplexIntegral n β f) := by
  exact measurable_orderedSimplexIntegral_of_measurable n id (fun _ => f) measurable_id
    (hf.comp measurable_snd)

end intervalIntegral

import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

set_option linter.style.header false

/-!
# Measurable bounded regularity for ordered-simplex integrands

The shuffle theorem only needs enough regularity to make every recursively exposed boundary
integrand interval integrable.  Global continuity is stronger than necessary.  This file packages a
weaker condition suited to finite chamber selections: global measurability together with uniform
boundedness on every centered finite-dimensional cube.

The condition is stable under fixing the outermost coordinate and under the finite products and
coordinate selections needed by the shuffle constructions.
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

/-- Prepending one coordinate sends a smaller centered cube into a larger one whenever the
new coordinate also lies within the larger radius. -/
theorem finCons_mem_orderedSimplexTimeCube {n : ℕ} {R S t : ℝ}
    {rest : Fin n → ℝ} (hRS : R ≤ S) (ht : |t| ≤ S)
    (hrest : rest ∈ orderedSimplexTimeCube n R) :
    Fin.cons t rest ∈ orderedSimplexTimeCube (n + 1) S := by
  rw [orderedSimplexTimeCube, Set.mem_Icc] at hrest ⊢
  constructor
  · intro i
    refine Fin.cases ((neg_le_neg ht).trans (neg_abs_le t)) (fun j => ?_) i
    exact (neg_le_neg hRS).trans (hrest.1 j)
  · intro i
    refine Fin.cases ((le_abs_self t).trans ht) (fun j => ?_) i
    exact (hrest.2 j).trans hRS

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

/-- Pulling back along a selection of finite coordinates preserves measurable local boundedness.
The coordinate selection need not be injective. -/
theorem MeasurableLocallyBounded.comp_finCoordinateSelection {m n : ℕ}
    {f : (Fin m → ℝ) → ℂ} (hf : MeasurableLocallyBounded f) (σ : Fin m → Fin n) :
    MeasurableLocallyBounded (fun τ : Fin n → ℝ => f (fun i => τ (σ i))) := by
  have hσ : Continuous (fun τ : Fin n → ℝ => fun i : Fin m => τ (σ i)) :=
    continuous_pi fun i => continuous_apply (σ i)
  refine ⟨hf.1.comp hσ.measurable, ?_⟩
  intro R hR
  obtain ⟨C, hC0, hC⟩ := hf.2 R hR
  refine ⟨C, hC0, ?_⟩
  intro τ hτ
  apply hC
  rw [orderedSimplexTimeCube, Set.mem_Icc] at hτ ⊢
  exact ⟨fun i => hτ.1 (σ i), fun i => hτ.2 (σ i)⟩

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
  exact hC _ (finCons_mem_orderedSimplexTimeCube
    (le_max_left R |t|) (le_max_right R |t|) hrest)

/-- Pick a representative of a finite-dimensional signature fiber when it is inhabited.
Unrealized fibers use the zero time assignment. -/
noncomputable def finiteSignatureBase {n : ℕ} {ι : Type*}
    (signature : (Fin n → ℝ) → ι) (s : ι) : Fin n → ℝ := by
  classical
  exact if h : ∃ σ : Fin n → ℝ, signature σ = s then
    Classical.choose h
  else
    0

/-- The chosen representative has the requested signature whenever its fiber is nonempty. -/
theorem finiteSignatureBase_signature_eq_of_exists {n : ℕ} {ι : Type*}
    (signature : (Fin n → ℝ) → ι) (s : ι)
    (h : ∃ σ : Fin n → ℝ, signature σ = s) :
    signature (finiteSignatureBase signature s) = s := by
  classical
  simp only [finiteSignatureBase, dite_eq_left h]
  exact Classical.choose_spec h

/-- Every assignment shares its signature with the representative of its own fiber. -/
theorem finiteSignatureBase_signature_eq {n : ℕ} {ι : Type*}
    (signature : (Fin n → ℝ) → ι) (σ : Fin n → ℝ) :
    signature (finiteSignatureBase signature (signature σ)) = signature σ :=
  finiteSignatureBase_signature_eq_of_exists signature (signature σ) ⟨σ, rfl⟩

/-- A finite measurable signature selects one of finitely many continuous branches
measurably, without assuming continuity across signature boundaries. -/
theorem measurable_of_finite_continuous_signature
    {ι : Type*} [Finite ι] {n : ℕ}
    (signature : (Fin n → ℝ) → ι)
    (hFiber : ∀ s : ι,
      MeasurableSet {σ : Fin n → ℝ | signature σ = s})
    (f : (Fin n → ℝ) → ℂ)
    (branch : ι → (Fin n → ℝ) → ℂ)
    (hContinuous : ∀ s, Continuous (branch s))
    (hSelect : ∀ σ, f σ = branch (signature σ) σ) :
    Measurable f := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hsum : f = fun σ : Fin n → ℝ =>
      ∑ s : ι, if signature σ = s then branch s σ else 0 := by
    funext σ
    simp [hSelect σ]
  rw [hsum]
  apply Finset.measurable_sum
  intro s _
  exact Measurable.ite (hFiber s) (hContinuous s).measurable measurable_const

end intervalIntegral

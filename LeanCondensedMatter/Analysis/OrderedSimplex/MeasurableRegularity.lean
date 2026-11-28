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
coordinate selections needed by the shuffle constructions. It also gives uniform bounds and interval
integrability for recursively exposed boundaries, and finite-sum linearity of the oriented integral.
The rough bound uses the cube volume scale `|β|^n`, since only finiteness is needed.
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

/-- Measurable local boundedness is preserved by addition. -/
theorem MeasurableLocallyBounded.add {n : ℕ} {f g : (Fin n → ℝ) → ℂ}
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    MeasurableLocallyBounded (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro R hR
  obtain ⟨C, hC0, hC⟩ := hf.2 R hR
  obtain ⟨D, hD0, hD⟩ := hg.2 R hR
  exact ⟨C + D, add_nonneg hC0 hD0, fun x hx =>
    (norm_add_le _ _).trans (add_le_add (hC x hx) (hD x hx))⟩

/-- Finite sums preserve measurable local boundedness. -/
theorem MeasurableLocallyBounded.finsetSum {ι : Type*} {n : ℕ} (s : Finset ι)
    (f : ι → (Fin n → ℝ) → ℂ) (hf : ∀ i ∈ s, MeasurableLocallyBounded (f i)) :
    MeasurableLocallyBounded (fun x => ∑ i ∈ s, f i x) := by
  simp_rw [← Finset.sum_apply]
  exact Finset.sum_induction f MeasurableLocallyBounded
    (fun _ _ ha hb => ha.add hb) (measurableLocallyBounded_const (n := n) 0) hf

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

/-- Every assignment shares its signature with the representative of its own fiber. -/
theorem finiteSignatureBase_signature_eq {n : ℕ} {ι : Type*}
    (signature : (Fin n → ℝ) → ι) (σ : Fin n → ℝ) :
    signature (finiteSignatureBase signature (signature σ)) = signature σ := by
  classical
  have h : ∃ σ' : Fin n → ℝ, signature σ' = signature σ := ⟨σ, rfl⟩
  simp only [finiteSignatureBase, dite_eq_left h]
  exact Classical.choose_spec h

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


/-- A measurable finite signature whose branches are continuous and agree with the
integrand on each signature fiber gives measurable local boundedness. -/
theorem measurableLocallyBounded_of_finite_continuous_signature
    {ι : Type*} [Finite ι] {n : ℕ}
    (signature : (Fin n → ℝ) → ι)
    (hFiber : ∀ s : ι,
      MeasurableSet {σ : Fin n → ℝ | signature σ = s})
    (f : (Fin n → ℝ) → ℂ)
    (branch : ι → (Fin n → ℝ) → ℂ)
    (hContinuous : ∀ s, Continuous (branch s))
    (hSelect : ∀ σ, f σ = branch (signature σ) σ) :
    MeasurableLocallyBounded f :=
  measurableLocallyBounded_of_finite_continuous_selection
    f branch
    (measurable_of_finite_continuous_signature
      signature hFiber f branch hContinuous hSelect)
    hContinuous (fun σ => ⟨signature σ, hSelect σ⟩)


/-- A uniform norm bound on the centered cube gives a rough `|β|^n` bound for the recursively
oriented ordered-simplex integral. -/
private theorem norm_orderedSimplexIntegral_le_of_cube_bound :
    ∀ (n : ℕ) (β : ℝ) (f : (Fin n → ℝ) → ℂ) (C : ℝ),
      0 ≤ C →
      (∀ x ∈ orderedSimplexTimeCube n |β|, ‖f x‖ ≤ C) →
      ‖orderedSimplexIntegral n β f‖ ≤ C * |β| ^ n
  | 0, β, f, C, _hC, hbound => by
      have hzero : (Fin.elim0 : Fin 0 → ℝ) ∈ orderedSimplexTimeCube 0 |β| := by
        rw [orderedSimplexTimeCube, Set.mem_Icc]
        exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      simpa using hbound (Fin.elim0 : Fin 0 → ℝ) hzero
  | n + 1, β, f, C, hC, hbound => by
      rw [orderedSimplexIntegral_succ]
      have houter : ∀ t ∈ Set.uIoc (0 : ℝ) β,
          ‖orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))‖ ≤
            C * |β| ^ n := by
        intro t ht
        have htAbs : |t| ≤ |β| := by
          simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc ht)
        have hslice : ∀ rest ∈ orderedSimplexTimeCube n |t|,
            ‖f (Fin.cons t rest)‖ ≤ C := by
          intro rest hrest
          exact hbound _ (finCons_mem_orderedSimplexTimeCube htAbs htAbs hrest)
        have hi := norm_orderedSimplexIntegral_le_of_cube_bound n t
          (fun rest => f (Fin.cons t rest)) C hC hslice
        calc
          ‖orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))‖ ≤
              C * |t| ^ n := hi
          _ ≤ C * |β| ^ n := by gcongr
      calc
        ‖∫ t in (0 : ℝ)..β,
            orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))‖ ≤
            (C * |β| ^ n) * |β - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const houter
        _ = C * |β| ^ (n + 1) := by
          rw [sub_zero, pow_succ]
          ring

/-- A measurable locally bounded integrand gives a uniform bound for its recursively exposed
ordered-simplex boundary on every finite oriented interval. -/
theorem MeasurableLocallyBounded.exists_norm_bound_orderedSimplexIntegral_boundary
    {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : MeasurableLocallyBounded f)
    (β : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.uIcc (0 : ℝ) β,
      ‖orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))‖ ≤ D := by
  obtain ⟨C, hC0, hC⟩ := hf.2 |β| (abs_nonneg β)
  let D := C * |β| ^ n
  have hD : 0 ≤ D := mul_nonneg hC0 (pow_nonneg (abs_nonneg β) n)
  refine ⟨D, hD, ?_⟩
  intro t ht
  have htAbs : |t| ≤ |β| := by
    simpa using abs_sub_left_of_mem_uIcc ht
  have hslice : ∀ rest ∈ orderedSimplexTimeCube n |t|,
      ‖f (Fin.cons t rest)‖ ≤ C := by
    intro rest hrest
    exact hC _ (finCons_mem_orderedSimplexTimeCube htAbs htAbs hrest)
  have hi := norm_orderedSimplexIntegral_le_of_cube_bound n t
    (fun rest => f (Fin.cons t rest)) C hC0 hslice
  calc
    ‖orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))‖ ≤
        C * |t| ^ n := hi
    _ ≤ C * |β| ^ n := by gcongr
    _ = D := rfl

/-- The recursively exposed outer boundary of a measurable locally bounded ordered-simplex
integrand is interval integrable on every finite oriented interval. -/
theorem MeasurableLocallyBounded.intervalIntegrable_orderedSimplexIntegral_boundary
    {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : MeasurableLocallyBounded f)
    (β : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest)))
      volume 0 β := by
  let H : ℝ → ℂ := fun t =>
    orderedSimplexIntegral n t (fun rest => f (Fin.cons t rest))
  have hMeas : Measurable H := by
    simpa [H] using
      measurable_orderedSimplexIntegral_of_measurable n id
        (fun t rest => f (Fin.cons t rest)) measurable_id
        (hf.1.comp (Continuous.finCons continuous_fst continuous_snd).measurable)
  obtain ⟨D, _hD, hNorm⟩ := hf.exists_norm_bound_orderedSimplexIntegral_boundary β
  have hIntOn : IntegrableOn H (Set.uIcc (0 : ℝ) β) := by
    exact MeasureTheory.IntegrableOn.of_bound
      isCompact_uIcc.measure_lt_top hMeas.aestronglyMeasurable D
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIcc
        (by simpa [H] using hNorm))
  exact hIntOn.intervalIntegrable

/-- **A finite sum commutes with `orderedSimplexIntegral` under measurable local boundedness.**

The continuity hypothesis of `orderedSimplexIntegral_finsetSum` is unavailable for integrands that
are only chamberwise continuous, which is the situation every mixed-order expansion produces.  Only
interval integrability of each recursively exposed boundary is actually needed, and that is exactly
what `MeasurableLocallyBounded` supplies. -/
theorem orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded {ι : Type*}
    (s : Finset ι) (n : ℕ) (β : ℝ) (f : ι → (Fin n → ℝ) → ℂ)
    (hf : ∀ i ∈ s, MeasurableLocallyBounded (f i)) :
    orderedSimplexIntegral n β (fun τ => ∑ i ∈ s, f i τ) =
      ∑ i ∈ s, orderedSimplexIntegral n β (f i) := by
  induction n generalizing β with
  | zero => simp
  | succ n ih =>
    have hcons : ∀ (t : ℝ), ∀ i ∈ s,
        MeasurableLocallyBounded (fun rest : Fin n → ℝ => f i (Fin.cons t rest)) :=
      fun t i hi => (hf i hi).finCons t
    have heq : ∀ t : ℝ,
        orderedSimplexIntegral n t (fun rest => ∑ i ∈ s, f i (Fin.cons t rest)) =
          ∑ i ∈ s, orderedSimplexIntegral n t (fun rest => f i (Fin.cons t rest)) := fun t =>
      ih t (fun i rest => f i (Fin.cons t rest)) (hcons t)
    rw [orderedSimplexIntegral_succ]
    simp_rw [heq]
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => (orderedSimplexIntegral_succ n β (f i)).symm
    · intro i hi
      exact (hf i hi).intervalIntegrable_orderedSimplexIntegral_boundary β

end intervalIntegral

import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity

set_option linter.style.header false

/-!
# Bounds and recursive interval integrability for measurable ordered-simplex integrands

A measurable locally bounded integrand remains controlled after exposing the outermost ordered
coordinate.  The rough bound below deliberately uses the surrounding cube volume scale `|β|^n`
rather than the sharper simplex factor `1 / n!`; only finiteness is needed by the shuffle theorem.
-/

namespace intervalIntegral

open MeasureTheory Set

/-- Enlarging the radius enlarges the centered ordered-simplex coordinate cube. -/
theorem orderedSimplexTimeCube_mono {n : ℕ} {R S : ℝ} (hRS : R ≤ S) :
    orderedSimplexTimeCube n R ⊆ orderedSimplexTimeCube n S := by
  intro x hx
  rw [orderedSimplexTimeCube, Set.mem_Icc] at hx ⊢
  exact ⟨fun i => (neg_le_neg hRS).trans (hx.1 i),
    fun i => (hx.2 i).trans hRS⟩

/-- Prepending a coordinate whose absolute value is at most the cube radius stays inside the cube. -/
theorem finCons_mem_orderedSimplexTimeCube {n : ℕ} {R t : ℝ}
    {rest : Fin n → ℝ} (ht : |t| ≤ R)
    (hrest : rest ∈ orderedSimplexTimeCube n R) :
    Fin.cons t rest ∈ orderedSimplexTimeCube (n + 1) R := by
  rw [orderedSimplexTimeCube, Set.mem_Icc] at hrest ⊢
  constructor
  · intro i
    induction i using Fin.cases with
    | zero => exact (neg_le_neg ht).trans (neg_abs_le t)
    | succ i => exact hrest.1 i
  · intro i
    induction i using Fin.cases with
    | zero => exact (le_abs_self t).trans ht
    | succ i => exact hrest.2 i

/-- Every point of the unoriented interval between `0` and `β` has absolute value at most `|β|`. -/
theorem abs_le_abs_of_mem_uIoc_zero {β t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) β) :
    |t| ≤ |β| := by
  rcases le_total (0 : ℝ) β with hβ | hβ
  · rw [uIoc_of_le hβ] at ht
    rw [abs_of_nonneg hβ, abs_of_nonneg ht.1.le]
    exact ht.2
  · rw [uIoc_of_ge hβ] at ht
    rw [abs_of_nonpos hβ, abs_of_nonpos ht.2]
    exact neg_le_neg ht.1.le

/-- Every point of the unoriented closed interval between `0` and `β` has absolute value at most
`|β|`. -/
theorem abs_le_abs_of_mem_uIcc_zero {β t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) β) :
    |t| ≤ |β| := by
  rcases le_total (0 : ℝ) β with hβ | hβ
  · rw [uIcc_of_le hβ] at ht
    rw [abs_of_nonneg hβ, abs_of_nonneg ht.1]
    exact ht.2
  · rw [uIcc_of_ge hβ] at ht
    rw [abs_of_nonpos hβ, abs_of_nonpos ht.2]
    exact neg_le_neg ht.1

/-- A uniform norm bound on the centered cube gives a rough `|β|^n` bound for the recursively
oriented ordered-simplex integral. -/
theorem norm_orderedSimplexIntegral_le_of_cube_bound :
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
        have htAbs : |t| ≤ |β| := abs_le_abs_of_mem_uIoc_zero ht
        have hslice : ∀ rest ∈ orderedSimplexTimeCube n |t|,
            ‖f (Fin.cons t rest)‖ ≤ C := by
          intro rest hrest
          apply hbound
          exact finCons_mem_orderedSimplexTimeCube htAbs
            (orderedSimplexTimeCube_mono htAbs hrest)
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

/-- Measurability of the recursively exposed outer boundary of an ordered-simplex integrand. -/
theorem measurable_orderedSimplexIntegral_boundary {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℂ) (hf : Measurable f) :
    Measurable (fun β : ℝ =>
      orderedSimplexIntegral n β (fun rest => f (Fin.cons β rest))) := by
  exact measurable_orderedSimplexIntegral_of_measurable n id
    (fun β rest => f (Fin.cons β rest)) measurable_id
    (hf.comp (Continuous.finCons continuous_fst continuous_snd).measurable)

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
  have htAbs : |t| ≤ |β| := abs_le_abs_of_mem_uIcc_zero ht
  have hslice : ∀ rest ∈ orderedSimplexTimeCube n |t|,
      ‖f (Fin.cons t rest)‖ ≤ C := by
    intro rest hrest
    apply hC
    exact finCons_mem_orderedSimplexTimeCube htAbs
      (orderedSimplexTimeCube_mono htAbs hrest)
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
    simpa [H] using measurable_orderedSimplexIntegral_boundary f hf.1
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

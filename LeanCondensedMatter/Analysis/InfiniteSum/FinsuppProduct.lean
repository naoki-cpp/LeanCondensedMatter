import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# A finite product of absolutely convergent series converges as a `Finsupp`-indexed multi-series

The finite-cardinality induction keeps each recursive theorem small. The common successor step is
split into a pure `Fin (k + 1)`/`Option (Fin k)` reindexing theorem and a separate product-of-series
theorem.
-/

namespace Finsupp

private theorem hasSum_prod_equiv
    {α β R : Type*} [Fintype α] [Fintype β] [NormedCommRing R]
    (e : α ≃ β) (f : β → ℕ → R) (a : β → R)
    (h : HasSum (fun n : α →₀ ℕ => ∏ i : α, f (e i) (n i)) (∏ i : α, a (e i))) :
    HasSum (fun n : β →₀ ℕ => ∏ i : β, f i (n i)) (∏ i : β, a i) := by
  have hreindex : (fun n : β →₀ ℕ => ∏ i : β, f i (n i)) =
      (fun m : α →₀ ℕ => ∏ i : α, f (e i) (m i)) ∘ Finsupp.equivMapDomain e.symm := by
    funext n
    simp only [Function.comp_apply, Finsupp.equivMapDomain_apply]
    symm
    exact Fintype.prod_equiv e (fun i => f (e i) (n (e i))) (fun j => f j (n j))
      (fun i => by simp)
  have h' : HasSum (fun n : β →₀ ℕ => ∏ i : β, f i (n i)) (∏ i : α, a (e i)) := by
    rw [hreindex]
    exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft e.symm)).mpr h
  have hprod : (∏ i : α, a (e i)) = ∏ i : β, a i :=
    Fintype.prod_equiv e (fun i => a (e i)) a (fun i => rfl)
  rwa [hprod] at h'

private theorem prod_option_finsupp_eq
    {α R : Type*} [Fintype α] [CommMonoid R]
    (f : Option α → ℕ → R) :
    (fun n : Option α →₀ ℕ => ∏ i : Option α, f i (n i)) =
      (fun p : ℕ × (α →₀ ℕ) =>
        f none p.1 * ∏ i : α, f (Option.some i) (p.2 i)) ∘ Finsupp.optionEquiv := by
  funext n
  simp only [Function.comp_apply, Finsupp.optionEquiv_apply]
  rw [Fintype.prod_option]
  congr 1

private theorem hasSum_prod_option_reindex
    {α R : Type*} [Fintype α] [NormedCommRing R]
    (f : Option α → ℕ → R) (a : Option α → R)
    (hprod : HasSum
      (fun p : ℕ × (α →₀ ℕ) =>
        f none p.1 * ∏ i : α, f (Option.some i) (p.2 i))
      (a none * ∏ i : α, a (Option.some i))) :
    HasSum (fun n : Option α →₀ ℕ => ∏ i : Option α, f i (n i))
      (∏ i : Option α, a i) := by
  rw [prod_option_finsupp_eq f]
  simpa only [Fintype.prod_option] using
    ((Equiv.hasSum_iff Finsupp.optionEquiv).mpr hprod)

private theorem hasSum_prod_fin_zero
    {R : Type*} [NormedCommRing R] (f : Fin 0 → ℕ → R) (a : Fin 0 → R) :
    HasSum (fun n : Fin 0 →₀ ℕ => ∏ i : Fin 0, f i (n i)) (∏ i : Fin 0, a i) := by
  have hzero : ∀ n : Fin 0 →₀ ℕ, n = 0 := fun n => by ext i; exact i.elim0
  have hsum : HasSum (fun n : Fin 0 →₀ ℕ => ∏ i : Fin 0, f i (n i))
      (∏ i : Fin 0, f i ((0 : Fin 0 →₀ ℕ) i)) :=
    hasSum_single (0 : Fin 0 →₀ ℕ) (fun n hn => absurd (hzero n) hn)
  simpa using hsum

private def finSuccFamily {k : ℕ} {α : Type*} (f : Fin (k + 1) → α) : Option (Fin k) → α
  | none => f 0
  | Option.some i => f i.succ

@[simp]
private theorem finSuccFamily_none {k : ℕ} {α : Type*} (f : Fin (k + 1) → α) :
    finSuccFamily f none = f 0 := rfl

@[simp]
private theorem finSuccFamily_some {k : ℕ} {α : Type*} (f : Fin (k + 1) → α) (i : Fin k) :
    finSuccFamily f (Option.some i) = f i.succ := rfl

private theorem prod_finSuccFamily
    {k : ℕ} {R : Type*} [CommMonoid R] (a : Fin (k + 1) → R) :
    (∏ i : Option (Fin k), finSuccFamily a i) = ∏ i : Fin (k + 1), a i := by
  rw [Fintype.prod_option, Fin.prod_univ_succ]
  rfl

private theorem prod_finSucc_finsupp_eq
    {k : ℕ} {R : Type*} [CommMonoid R] (f : Fin (k + 1) → ℕ → R) :
    (fun n : Fin (k + 1) →₀ ℕ => ∏ i : Fin (k + 1), f i (n i)) =
      (fun m : Option (Fin k) →₀ ℕ =>
        ∏ i : Option (Fin k), finSuccFamily f i (m i)) ∘
        Finsupp.equivMapDomain (finSuccEquiv k) := by
  funext n
  simp only [Function.comp_apply]
  apply Fintype.prod_equiv (finSuccEquiv k) (fun i => f i (n i))
    (fun j => finSuccFamily f j ((Finsupp.equivMapDomain (finSuccEquiv k) n) j))
  intro i
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  refine Fin.cases ?_ ?_ i
  · simp [finSuccFamily]
  · intro j
    simp [finSuccFamily]

private theorem hasSum_prod_finSucc_reindex
    {k : ℕ} {R : Type*} [NormedCommRing R]
    (f : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R)
    (hOption : HasSum
      (fun n : Option (Fin k) →₀ ℕ =>
        ∏ i : Option (Fin k), finSuccFamily f i (n i))
      (∏ i : Option (Fin k), finSuccFamily a i)) :
    HasSum (fun n : Fin (k + 1) →₀ ℕ => ∏ i : Fin (k + 1), f i (n i))
      (∏ i : Fin (k + 1), a i) := by
  rw [prod_finSucc_finsupp_eq f]
  have h := (Equiv.hasSum_iff (Finsupp.equivCongrLeft (finSuccEquiv k))).mpr hOption
  rwa [prod_finSuccFamily] at h

private theorem hasSum_prod_finSucc_option
    {k : ℕ} {R : Type*} [NormedCommRing R] [CompleteSpace R]
    (f : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R)
    (hhead : HasSum (f 0) (a 0))
    (htail : HasSum (fun n : Fin k →₀ ℕ => ∏ i : Fin k, f i.succ (n i))
      (∏ i : Fin k, a i.succ))
    (habsHead : Summable (fun n => ‖f 0 n‖))
    (habsTail : Summable (fun n : Fin k →₀ ℕ => ‖∏ i : Fin k, f i.succ (n i)‖)) :
    HasSum (fun n : Option (Fin k) →₀ ℕ =>
      ∏ i : Option (Fin k), finSuccFamily f i (n i))
      (∏ i : Option (Fin k), finSuccFamily a i) := by
  let tail : (Fin k →₀ ℕ) → R :=
    fun n => ∏ i : Fin k, f i.succ (n i)
  have hmul : Summable
      (fun p : ℕ × (Fin k →₀ ℕ) => f 0 p.1 * tail p.2) :=
    summable_mul_of_summable_norm habsHead habsTail
  have htail' : HasSum tail (∏ i : Fin k, a i.succ) := htail
  have hprod : HasSum
      (fun p : ℕ × (Fin k →₀ ℕ) => f 0 p.1 * tail p.2)
      (a 0 * ∏ i : Fin k, a i.succ) :=
    hhead.mul htail' hmul
  exact hasSum_prod_option_reindex (finSuccFamily f) (finSuccFamily a) hprod

private theorem hasSum_prod_fin_succ
    {k : ℕ} {R : Type*} [NormedCommRing R] [CompleteSpace R]
    (f : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R)
    (hhead : HasSum (f 0) (a 0))
    (htail : HasSum (fun n : Fin k →₀ ℕ => ∏ i : Fin k, f i.succ (n i))
      (∏ i : Fin k, a i.succ))
    (habsHead : Summable (fun n => ‖f 0 n‖))
    (habsTail : Summable (fun n : Fin k →₀ ℕ => ‖∏ i : Fin k, f i.succ (n i)‖)) :
    HasSum (fun n : Fin (k + 1) →₀ ℕ => ∏ i : Fin (k + 1), f i (n i))
      (∏ i : Fin (k + 1), a i) :=
  hasSum_prod_finSucc_reindex f a
    (hasSum_prod_finSucc_option f a hhead htail habsHead habsTail)

/-! ## The nonnegative-real case -/

section Nonneg

variable {ι : Type*}

private theorem hasSum_prod_nonneg_fin_succ
    (k : ℕ) (g : Fin (k + 1) → ℕ → ℝ) (b : Fin (k + 1) → ℝ)
    (hg : ∀ i, HasSum (g i) (b i)) (hnn : ∀ i n, 0 ≤ g i n)
    (htail : HasSum (fun n : Fin k →₀ ℕ => ∏ i : Fin k, g i.succ (n i))
      (∏ i : Fin k, b i.succ)) :
    HasSum (fun n : Fin (k + 1) →₀ ℕ => ∏ i : Fin (k + 1), g i (n i))
      (∏ i : Fin (k + 1), b i) := by
  apply hasSum_prod_fin_succ g b (hg 0) htail
  · rw [show (fun n => ‖g 0 n‖) = g 0 from
      funext fun n => Real.norm_of_nonneg (hnn 0 n)]
    exact (hg 0).summable
  · rw [show (fun n : Fin k →₀ ℕ => ‖∏ i : Fin k, g i.succ (n i)‖) =
        (fun n => ∏ i : Fin k, g i.succ (n i)) from
      funext fun n => Real.norm_of_nonneg
        (Finset.prod_nonneg fun i _ => hnn i.succ (n i))]
    exact htail.summable

private theorem hasSum_prod_nonneg_fin (k : ℕ) (g : Fin k → ℕ → ℝ) (b : Fin k → ℝ)
    (hg : ∀ i, HasSum (g i) (b i)) (hnn : ∀ i n, 0 ≤ g i n) :
    HasSum (fun n : Fin k →₀ ℕ => ∏ i : Fin k, g i (n i)) (∏ i : Fin k, b i) := by
  induction k with
  | zero => exact hasSum_prod_fin_zero g b
  | succ k ih =>
      apply hasSum_prod_nonneg_fin_succ k g b hg hnn
      exact ih (fun i => g i.succ) (fun i => b i.succ)
        (fun i => hg i.succ) (fun i n => hnn i.succ n)

/-- **The nonnegative-real finite product of series converges** to the product of the individual
sums, as a `Finsupp`-indexed multi-series. -/
theorem hasSum_prod_nonneg [Fintype ι] (g : ι → ℕ → ℝ) (b : ι → ℝ)
    (hg : ∀ i, HasSum (g i) (b i)) (hnn : ∀ i n, 0 ≤ g i n) :
    HasSum (fun n : ι →₀ ℕ => ∏ i : ι, g i (n i)) (∏ i : ι, b i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  apply hasSum_prod_equiv e.symm g b
  exact hasSum_prod_nonneg_fin (Fintype.card ι)
    (fun i => g (e.symm i)) (fun i => b (e.symm i))
    (fun i => hg (e.symm i)) (fun i n => hnn (e.symm i) n)

end Nonneg

/-! ## The general `NormedCommRing` case -/

section General

variable {ι : Type*} {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

omit [CompleteSpace R] in
private theorem summable_norm_prod [Fintype ι] (f : ι → ℕ → R)
    (habs : ∀ i, Summable (fun k => ‖f i k‖)) :
    Summable (fun n : ι →₀ ℕ => ‖∏ i : ι, f i (n i)‖) := by
  have hbound : HasSum (fun n : ι →₀ ℕ => ∏ i : ι, ‖f i (n i)‖)
      (∏ i : ι, ∑' k, ‖f i k‖) :=
    hasSum_prod_nonneg (fun i k => ‖f i k‖) (fun i => ∑' k, ‖f i k‖)
      (fun i => (habs i).hasSum) (fun i n => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbound.summable
  exact Finset.norm_prod_le Finset.univ (fun i => f i (n i))

private theorem hasSum_prod_fin_succ_general
    (k : ℕ) (f : Fin (k + 1) → ℕ → R) (a : Fin (k + 1) → R)
    (hf : ∀ i, HasSum (f i) (a i)) (habs : ∀ i, Summable (fun n => ‖f i n‖))
    (htail : HasSum (fun n : Fin k →₀ ℕ => ∏ i : Fin k, f i.succ (n i))
      (∏ i : Fin k, a i.succ)) :
    HasSum (fun n : Fin (k + 1) →₀ ℕ => ∏ i : Fin (k + 1), f i (n i))
      (∏ i : Fin (k + 1), a i) := by
  have habsTail : Summable
      (fun n : Fin k →₀ ℕ => ‖∏ i : Fin k, f i.succ (n i)‖) :=
    summable_norm_prod (fun i : Fin k => f i.succ) (fun i => habs i.succ)
  exact hasSum_prod_fin_succ f a (hf 0) htail (habs 0) habsTail

private theorem hasSum_prod_fin (k : ℕ) (f : Fin k → ℕ → R) (a : Fin k → R)
    (hf : ∀ i, HasSum (f i) (a i)) (habs : ∀ i, Summable (fun n => ‖f i n‖)) :
    HasSum (fun n : Fin k →₀ ℕ => ∏ i : Fin k, f i (n i)) (∏ i : Fin k, a i) := by
  induction k with
  | zero => exact hasSum_prod_fin_zero f a
  | succ k ih =>
      apply hasSum_prod_fin_succ_general k f a hf habs
      exact ih (fun i => f i.succ) (fun i => a i.succ)
        (fun i => hf i.succ) (fun i => habs i.succ)

/-- **A finite product of absolutely convergent series converges** as a `Finsupp`-indexed
multi-series. -/
theorem hasSum_prod [Fintype ι] (f : ι → ℕ → R) (a : ι → R) (hf : ∀ i, HasSum (f i) (a i))
    (habs : ∀ i, Summable (fun k => ‖f i k‖)) :
    HasSum (fun n : ι →₀ ℕ => ∏ i : ι, f i (n i)) (∏ i : ι, a i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  apply hasSum_prod_equiv e.symm f a
  exact hasSum_prod_fin (Fintype.card ι)
    (fun i => f (e.symm i)) (fun i => a (e.symm i))
    (fun i => hf (e.symm i)) (fun i => habs (e.symm i))

/-- **The geometric-series specialization**. -/
theorem hasSum_prod_geometric {R : Type*} [NormedField R] [CompleteSpace R] {ι : Type*}
    [Fintype ι] (q : ι → R) (hq : ∀ i, ‖q i‖ < 1) :
    HasSum (fun n : ι →₀ ℕ => ∏ i : ι, q i ^ n i) (∏ i : ι, (1 - q i)⁻¹) :=
  hasSum_prod (fun i k => q i ^ k) (fun i => (1 - q i)⁻¹)
    (fun i => hasSum_geometric_of_norm_lt_one (hq i))
    (fun i => by
      simp only [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hq i))

end General

end Finsupp

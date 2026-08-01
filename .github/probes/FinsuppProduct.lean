import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# A finite product of absolutely convergent series converges as a `Finsupp`-indexed multi-series

The proof uses `Fintype.induction_empty_option` directly. Its successor step matches
`Finsupp.optionEquiv`, avoiding the previous conversion through `Fin (Fintype.card ι)` and the
second `finSuccEquiv` reindexing layer.
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

private theorem hasSum_prod_option
    {α R : Type*} [Fintype α] [NormedCommRing R] [CompleteSpace R]
    (f : Option α → ℕ → R) (a : Option α → R)
    (hhead : HasSum (f none) (a none))
    (htail : HasSum (fun n : α →₀ ℕ => ∏ i : α, f (some i) (n i))
      (∏ i : α, a (some i)))
    (habsHead : Summable (fun n => ‖f none n‖))
    (habsTail : Summable (fun n : α →₀ ℕ => ‖∏ i : α, f (some i) (n i)‖)) :
    HasSum (fun n : Option α →₀ ℕ => ∏ i : Option α, f i (n i))
      (∏ i : Option α, a i) := by
  have hmul : Summable
      (fun p : ℕ × (α →₀ ℕ) => f none p.1 * ∏ i : α, f (some i) (p.2 i)) :=
    summable_mul_of_summable_norm habsHead habsTail
  have hprod : HasSum
      (fun p : ℕ × (α →₀ ℕ) => f none p.1 * ∏ i : α, f (some i) (p.2 i))
      (a none * ∏ i : α, a (some i)) := hhead.mul htail hmul
  have hreindex : (fun n : Option α →₀ ℕ => ∏ i : Option α, f i (n i)) =
      (fun p : ℕ × (α →₀ ℕ) => f none p.1 * ∏ i : α, f (some i) (p.2 i)) ∘
        Finsupp.optionEquiv := by
    funext n
    simp only [Function.comp_apply, Finsupp.optionEquiv_apply]
    rw [Fintype.prod_option]
  have hoption : HasSum (fun n : Option α →₀ ℕ => ∏ i : Option α, f i (n i))
      (a none * ∏ i : α, a (some i)) := by
    rw [hreindex]
    exact (Equiv.hasSum_iff Finsupp.optionEquiv).mpr hprod
  rwa [Fintype.prod_option] at hoption

/-! ## The nonnegative-real case -/

section Nonneg

variable {ι : Type*}

/-- **The nonnegative-real finite product of series converges** to the product of the individual
sums, as a `Finsupp`-indexed multi-series. -/
theorem hasSum_prod_nonneg [Fintype ι] (g : ι → ℕ → ℝ) (b : ι → ℝ)
    (hg : ∀ i, HasSum (g i) (b i)) (hnn : ∀ i n, 0 ≤ g i n) :
    HasSum (fun n : ι →₀ ℕ => ∏ i : ι, g i (n i)) (∏ i : ι, b i) := by
  classical
  refine @Fintype.induction_empty_option
    (fun κ _ => ∀ (g : κ → ℕ → ℝ) (b : κ → ℝ),
      (∀ i, HasSum (g i) (b i)) → (∀ i n, 0 ≤ g i n) →
      HasSum (fun n : κ →₀ ℕ => ∏ i : κ, g i (n i)) (∏ i : κ, b i))
    ?_ ?_ ?_ ι _ g b hg hnn
  · intro α β _ e h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    intro g b hg hnn
    exact hasSum_prod_equiv e g b
      (h (fun i => g (e i)) (fun i => b (e i))
        (fun i => hg (e i)) (fun i n => hnn (e i) n))
  · intro g b hg hnn
    have hzero : ∀ n : PEmpty →₀ ℕ, n = 0 := fun n => by ext i; exact i.elim
    have hsum : HasSum (fun n : PEmpty →₀ ℕ => ∏ i : PEmpty, g i (n i))
        (∏ i : PEmpty, g i ((0 : PEmpty →₀ ℕ) i)) :=
      hasSum_single (0 : PEmpty →₀ ℕ) (fun n hn => absurd (hzero n) hn)
    simpa using hsum
  · intro α _ h g b hg hnn
    have htail := h (fun i => g (some i)) (fun i => b (some i))
      (fun i => hg (some i)) (fun i n => hnn (some i) n)
    have hhead : HasSum (g none) (b none) := hg none
    have habsHead : Summable (fun n => ‖g none n‖) := by
      rw [show (fun n => ‖g none n‖) = g none from
        funext fun n => Real.norm_of_nonneg (hnn none n)]
      exact hhead.summable
    have habsTail : Summable (fun n : α →₀ ℕ => ‖∏ i : α, g (some i) (n i)‖) := by
      rw [show (fun n : α →₀ ℕ => ‖∏ i : α, g (some i) (n i)‖) =
          (fun n => ∏ i : α, g (some i) (n i)) from
        funext fun n => Real.norm_of_nonneg
          (Finset.prod_nonneg fun i _ => hnn (some i) (n i))]
      exact htail.summable
    exact hasSum_prod_option g b hhead htail habsHead habsTail

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

/-- **A finite product of absolutely convergent series converges** as a `Finsupp`-indexed
multi-series. -/
theorem hasSum_prod [Fintype ι] (f : ι → ℕ → R) (a : ι → R) (hf : ∀ i, HasSum (f i) (a i))
    (habs : ∀ i, Summable (fun k => ‖f i k‖)) :
    HasSum (fun n : ι →₀ ℕ => ∏ i : ι, f i (n i)) (∏ i : ι, a i) := by
  classical
  refine @Fintype.induction_empty_option
    (fun κ _ => ∀ (f : κ → ℕ → R) (a : κ → R),
      (∀ i, HasSum (f i) (a i)) → (∀ i, Summable (fun k => ‖f i k‖)) →
      HasSum (fun n : κ →₀ ℕ => ∏ i : κ, f i (n i)) (∏ i : κ, a i))
    ?_ ?_ ?_ ι _ f a hf habs
  · intro α β _ e h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    intro f a hf habs
    exact hasSum_prod_equiv e f a
      (h (fun i => f (e i)) (fun i => a (e i))
        (fun i => hf (e i)) (fun i => habs (e i)))
  · intro f a hf habs
    have hzero : ∀ n : PEmpty →₀ ℕ, n = 0 := fun n => by ext i; exact i.elim
    have hsum : HasSum (fun n : PEmpty →₀ ℕ => ∏ i : PEmpty, f i (n i))
        (∏ i : PEmpty, f i ((0 : PEmpty →₀ ℕ) i)) :=
      hasSum_single (0 : PEmpty →₀ ℕ) (fun n hn => absurd (hzero n) hn)
    simpa using hsum
  · intro α _ h f a hf habs
    have htail := h (fun i => f (some i)) (fun i => a (some i))
      (fun i => hf (some i)) (fun i => habs (some i))
    have hhead : HasSum (f none) (a none) := hf none
    have habsTail : Summable (fun n : α →₀ ℕ => ‖∏ i : α, f (some i) (n i)‖) :=
      summable_norm_prod (fun i => f (some i)) (fun i => habs (some i))
    exact hasSum_prod_option f a hhead htail (habs none) habsTail

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

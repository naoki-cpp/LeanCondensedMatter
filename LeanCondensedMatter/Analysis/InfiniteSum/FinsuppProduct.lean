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

For finitely many index-`i` series `f i : ℕ → R`, each converging (`HasSum (f i) (a i)`) and
absolutely so (`Summable (fun k => ‖f i k‖)`), the multi-index series over `n : ι →₀ ℕ` formed by
taking one term per index, `∏ i, f i (n i)`, converges to the product of the individual sums,
`∏ i, a i` (`Finsupp.hasSum_prod`). The geometric-series specialization
`Finsupp.hasSum_prod_geometric` is the multi-mode partition-function identity `Σ_n ∏ᵢ qᵢ^{n(i)} =
∏ᵢ (1 - qᵢ)⁻¹` that motivated extracting this file, but the theorem itself is pure convergence
theory: no physics, no reference to any occupation-number type or Boltzmann weight.

This is a general-math fact belonging upstream of any one physical use, per this project's
"general-purpose lemmas go in the foundational layer, not the first physics file that happened to
need them" convention (`Analysis/` is general mathematical infrastructure; `SecondQuantization/`
depends on it, never the reverse).

The proof reindexes along `Fintype.equivFin ι` once, then proceeds by ordinary induction on the
`Fin`-indexed count, splitting off one index at a time via `Finsupp.optionEquiv : (Option α →₀ M) ≃
M × (α →₀ M)` and `HasSum.mul`. The nonnegative-real case (`hasSum_prod_nonneg`) is proved first and
separately, since there norm-summability is free from `HasSum.summable`; the general-ring case
reuses it (applied to the termwise norms) to supply the norm-summability `HasSum.mul` needs at each
inductive step.
-/

namespace Finsupp

/-! ## The nonnegative-real case -/

section Nonneg

variable {ι : Type*}

set_option maxHeartbeats 0 in
-- Unbounded: the induction below carries many local definitions through several rewrite
-- steps, which pushes elaboration past the default heartbeat budget even though each step is
-- individually simple.
private theorem hasSum_prod_nonneg_fin (k : ℕ) (g : Fin k → ℕ → ℝ) (b : Fin k → ℝ)
    (hg : ∀ i, HasSum (g i) (b i)) (hnn : ∀ i n, 0 ≤ g i n) :
    HasSum (fun n : Fin k →₀ ℕ => ∏ i, g i (n i)) (∏ i, b i) := by
  induction k with
  | zero =>
    have hzero : ∀ n : Fin 0 →₀ ℕ, n = 0 := fun n => by ext i; exact i.elim0
    have hval : (∏ i : Fin 0, g i ((0 : Fin 0 →₀ ℕ) i)) = 1 := by simp
    have hsum : HasSum (fun n : Fin 0 →₀ ℕ => ∏ i, g i (n i))
        (∏ i : Fin 0, g i ((0 : Fin 0 →₀ ℕ) i)) :=
      hasSum_single (0 : Fin 0 →₀ ℕ) (fun n' hn' => absurd (hzero n') hn')
    rw [hval] at hsum
    simp only [Fin.prod_univ_zero] at hsum; exact hsum
  | succ k ih =>
    set g' : Fin k → ℕ → ℝ := fun i => g i.succ with hg'def
    have hg' : ∀ i, HasSum (g' i) (b i.succ) := fun i => hg i.succ
    have H2 : HasSum (fun n : Fin k →₀ ℕ => ∏ i, g' i (n i)) (∏ i : Fin k, b i.succ) :=
      ih g' (fun i => b i.succ) hg' (fun i n => hnn i.succ n)
    clear_value g'
    set gOpt : Option (Fin k) → ℕ → ℝ := fun o => o.elim (g 0) g' with hgOptdef
    have hgOptnone : gOpt none = g 0 := rfl
    have hgOptsome : gOpt ∘ Option.some = g' := rfl
    have H1 : HasSum (gOpt none) (b 0) := hg 0
    clear_value gOpt
    have hnn1 : ∀ x : ℕ, 0 ≤ gOpt none x := fun x => by rw [hgOptnone]; exact hnn 0 x
    have hnn2 : ∀ n : Fin k →₀ ℕ, 0 ≤ ∏ i, g' i (n i) :=
      fun n => Finset.prod_nonneg fun i _ => by rw [hg'def]; exact hnn i.succ (n i)
    have hnorm1 : Summable (fun x => ‖gOpt none x‖) := by
      rw [show (fun x => ‖gOpt none x‖) = gOpt none from
        funext fun x => Real.norm_of_nonneg (hnn1 x)]
      exact H1.summable
    have hnorm2 : Summable (fun n : Fin k →₀ ℕ => ‖∏ i, g' i (n i)‖) := by
      rw [show (fun n : Fin k →₀ ℕ => ‖∏ i, g' i (n i)‖) = (fun n => ∏ i, g' i (n i)) from
        funext fun n => Real.norm_of_nonneg (hnn2 n)]
      exact H2.summable
    have hmulsummable : Summable
        (fun p : ℕ × (Fin k →₀ ℕ) => gOpt none p.1 * ∏ i, g' i (p.2 i)) :=
      summable_mul_of_summable_norm hnorm1 hnorm2
    have H3 : HasSum (fun p : ℕ × (Fin k →₀ ℕ) => gOpt none p.1 * ∏ i, g' i (p.2 i))
        (b 0 * ∏ i : Fin k, b i.succ) := H1.mul H2 hmulsummable
    have hoption : (fun m : Option (Fin k) →₀ ℕ => ∏ i, gOpt i (m i)) =
        (fun p : ℕ × (Fin k →₀ ℕ) => gOpt none p.1 * ∏ i, g' i (p.2 i)) ∘
          Finsupp.optionEquiv := by
      funext m
      simp only [Function.comp_apply, Finsupp.optionEquiv_apply]
      rw [Fintype.prod_option (fun i => gOpt i (m i))]
      congr 1
      all_goals first
        | rfl
        | exact Finset.prod_congr rfl fun i _ => by rw [← hgOptsome]; rfl
    have H4 : HasSum (fun m : Option (Fin k) →₀ ℕ => ∏ i, gOpt i (m i))
        (b 0 * ∏ i : Fin k, b i.succ) := by
      rw [hoption]
      exact (Equiv.hasSum_iff Finsupp.optionEquiv).mpr H3
    have hcomp : gOpt ∘ finSuccEquiv k = g := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [hgOptdef, finSuccEquiv_zero]
      · intro j
        simp [hgOptdef, finSuccEquiv_succ, hg'def]
    have hreindex : (fun n : Fin (k + 1) →₀ ℕ => ∏ i, g i (n i)) =
        (fun m : Option (Fin k) →₀ ℕ => ∏ i, gOpt i (m i)) ∘
          Finsupp.equivMapDomain (finSuccEquiv k) := by
      funext n
      simp only [Function.comp_apply]
      apply Fintype.prod_equiv (finSuccEquiv k) (fun i => g i (n i))
        (fun j => gOpt j ((Finsupp.equivMapDomain (finSuccEquiv k) n) j))
      intro i
      have hp := congrFun hcomp i
      simp only [Function.comp_apply] at hp
      rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, hp]
    have H5 : HasSum (fun n : Fin (k + 1) →₀ ℕ => ∏ i, g i (n i))
        (b 0 * ∏ i : Fin k, b i.succ) := by
      rw [hreindex]
      exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft (finSuccEquiv k))).mpr H4
    rw [Fin.prod_univ_succ]
    exact H5

/-- **The nonnegative-real finite product of series converges** to the product of the individual
sums, as a `Finsupp`-indexed multi-series: `Σ_{n : ι →₀ ℕ} ∏ᵢ g i (n i) = ∏ᵢ b i`, given each
one-index series `HasSum (g i) (b i)` and nonnegativity (`0 ≤ g i n`, giving norm-summability for
free from `HasSum.summable`). -/
theorem hasSum_prod_nonneg [Fintype ι] (g : ι → ℕ → ℝ) (b : ι → ℝ)
    (hg : ∀ i, HasSum (g i) (b i)) (hnn : ∀ i n, 0 ≤ g i n) :
    HasSum (fun n : ι →₀ ℕ => ∏ i, g i (n i)) (∏ i, b i) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hedef
  have H := hasSum_prod_nonneg_fin (Fintype.card ι) (fun i => g (e.symm i)) (fun i => b (e.symm i))
    (fun i => hg (e.symm i)) (fun i n => hnn (e.symm i) n)
  have hreindex : (fun n : ι →₀ ℕ => ∏ i, g i (n i)) =
      (fun m : Fin (Fintype.card ι) →₀ ℕ => ∏ i, g (e.symm i) (m i)) ∘
        Finsupp.equivMapDomain e := by
    funext n
    simp only [Function.comp_apply, Finsupp.equivMapDomain_apply]
    exact Fintype.prod_equiv e (fun i => g i (n i)) (fun i => g (e.symm i) (n (e.symm i)))
      (fun i => by simp)
  have H' : HasSum (fun n : ι →₀ ℕ => ∏ i, g i (n i))
      (∏ i : Fin (Fintype.card ι), b (e.symm i)) := by
    rw [hreindex]
    exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft e)).mpr H
  have hprodeq : (∏ i : Fin (Fintype.card ι), b (e.symm i)) = ∏ i, b i :=
    Fintype.prod_equiv e.symm (fun i => b (e.symm i)) b (fun i => by simp)
  rwa [hprodeq] at H'

end Nonneg

/-! ## The general `NormedCommRing` case -/

section General

variable {ι : Type*} {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

omit [CompleteSpace R] in
private theorem summable_norm_prod [Fintype ι] (f : ι → ℕ → R)
    (habs : ∀ i, Summable (fun k => ‖f i k‖)) :
    Summable (fun n : ι →₀ ℕ => ‖∏ i, f i (n i)‖) := by
  have hbound : HasSum (fun n : ι →₀ ℕ => ∏ i, ‖f i (n i)‖) (∏ i, ∑' k, ‖f i k‖) :=
    hasSum_prod_nonneg (fun i k => ‖f i k‖) (fun i => ∑' k, ‖f i k‖)
      (fun i => (habs i).hasSum) (fun i n => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbound.summable
  exact Finset.norm_prod_le Finset.univ (fun i => f i (n i))

set_option maxHeartbeats 0 in
-- Unbounded: same reason as `hasSum_prod_nonneg_fin` above.
private theorem hasSum_prod_fin (k : ℕ) (f : Fin k → ℕ → R) (a : Fin k → R)
    (hf : ∀ i, HasSum (f i) (a i)) (habs : ∀ i, Summable (fun n => ‖f i n‖)) :
    HasSum (fun n : Fin k →₀ ℕ => ∏ i, f i (n i)) (∏ i, a i) := by
  induction k with
  | zero =>
    have hzero : ∀ n : Fin 0 →₀ ℕ, n = 0 := fun n => by ext i; exact i.elim0
    have hval : (∏ i : Fin 0, f i ((0 : Fin 0 →₀ ℕ) i)) = 1 := by simp
    have hsum : HasSum (fun n : Fin 0 →₀ ℕ => ∏ i, f i (n i))
        (∏ i : Fin 0, f i ((0 : Fin 0 →₀ ℕ) i)) :=
      hasSum_single (0 : Fin 0 →₀ ℕ) (fun n' hn' => absurd (hzero n') hn')
    rw [hval] at hsum
    simp only [Fin.prod_univ_zero] at hsum; exact hsum
  | succ k ih =>
    set f' : Fin k → ℕ → R := fun i => f i.succ with hf'def
    have hf' : ∀ i, HasSum (f' i) (a i.succ) := fun i => hf i.succ
    have habs' : ∀ i, Summable (fun n => ‖f' i n‖) := fun i => habs i.succ
    have H2 : HasSum (fun n : Fin k →₀ ℕ => ∏ i, f' i (n i)) (∏ i : Fin k, a i.succ) :=
      ih f' (fun i => a i.succ) hf' habs'
    have hnorm2 : Summable (fun n : Fin k →₀ ℕ => ‖∏ i, f' i (n i)‖) :=
      summable_norm_prod f' habs'
    clear_value f'
    set fOpt : Option (Fin k) → ℕ → R := fun o => o.elim (f 0) f' with hfOptdef
    have hfOptnone : fOpt none = f 0 := rfl
    have hfOptsome : fOpt ∘ Option.some = f' := rfl
    have H1 : HasSum (fOpt none) (a 0) := hf 0
    clear_value fOpt
    have hnorm1 : Summable (fun x => ‖fOpt none x‖) := by rw [hfOptnone]; exact habs 0
    have hmulsummable : Summable
        (fun p : ℕ × (Fin k →₀ ℕ) => fOpt none p.1 * ∏ i, f' i (p.2 i)) :=
      summable_mul_of_summable_norm hnorm1 hnorm2
    have H3 : HasSum (fun p : ℕ × (Fin k →₀ ℕ) => fOpt none p.1 * ∏ i, f' i (p.2 i))
        (a 0 * ∏ i : Fin k, a i.succ) := H1.mul H2 hmulsummable
    have hoption : (fun m : Option (Fin k) →₀ ℕ => ∏ i, fOpt i (m i)) =
        (fun p : ℕ × (Fin k →₀ ℕ) => fOpt none p.1 * ∏ i, f' i (p.2 i)) ∘
          Finsupp.optionEquiv := by
      funext m
      simp only [Function.comp_apply, Finsupp.optionEquiv_apply]
      rw [Fintype.prod_option (fun i => fOpt i (m i))]
      congr 1
      all_goals first
        | rfl
        | exact Finset.prod_congr rfl fun i _ => by rw [← hfOptsome]; rfl
    have H4 : HasSum (fun m : Option (Fin k) →₀ ℕ => ∏ i, fOpt i (m i))
        (a 0 * ∏ i : Fin k, a i.succ) := by
      rw [hoption]
      exact (Equiv.hasSum_iff Finsupp.optionEquiv).mpr H3
    have hcomp : fOpt ∘ finSuccEquiv k = f := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [hfOptdef, finSuccEquiv_zero]
      · intro j
        simp [hfOptdef, finSuccEquiv_succ, hf'def]
    have hreindex : (fun n : Fin (k + 1) →₀ ℕ => ∏ i, f i (n i)) =
        (fun m : Option (Fin k) →₀ ℕ => ∏ i, fOpt i (m i)) ∘
          Finsupp.equivMapDomain (finSuccEquiv k) := by
      funext n
      simp only [Function.comp_apply]
      apply Fintype.prod_equiv (finSuccEquiv k) (fun i => f i (n i))
        (fun j => fOpt j ((Finsupp.equivMapDomain (finSuccEquiv k) n) j))
      intro i
      have hp := congrFun hcomp i
      simp only [Function.comp_apply] at hp
      rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, hp]
    have H5 : HasSum (fun n : Fin (k + 1) →₀ ℕ => ∏ i, f i (n i))
        (a 0 * ∏ i : Fin k, a i.succ) := by
      rw [hreindex]
      exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft (finSuccEquiv k))).mpr H4
    rw [Fin.prod_univ_succ]
    exact H5

/-- **A finite product of absolutely convergent series converges** as a `Finsupp`-indexed
multi-series: `Σ_{n : ι →₀ ℕ} ∏ᵢ f i (n i) = ∏ᵢ a i`, given each one-index series `HasSum (f i)
(a i)` and absolute convergence (`Summable (fun k => ‖f i k‖)`). Pure convergence theory, over any
complete normed commutative ring. -/
theorem hasSum_prod [Fintype ι] (f : ι → ℕ → R) (a : ι → R) (hf : ∀ i, HasSum (f i) (a i))
    (habs : ∀ i, Summable (fun k => ‖f i k‖)) :
    HasSum (fun n : ι →₀ ℕ => ∏ i, f i (n i)) (∏ i, a i) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hedef
  have H := hasSum_prod_fin (Fintype.card ι) (fun i => f (e.symm i)) (fun i => a (e.symm i))
    (fun i => hf (e.symm i)) (fun i => habs (e.symm i))
  have hreindex : (fun n : ι →₀ ℕ => ∏ i, f i (n i)) =
      (fun m : Fin (Fintype.card ι) →₀ ℕ => ∏ i, f (e.symm i) (m i)) ∘
        Finsupp.equivMapDomain e := by
    funext n
    simp only [Function.comp_apply, Finsupp.equivMapDomain_apply]
    exact Fintype.prod_equiv e (fun i => f i (n i)) (fun i => f (e.symm i) (n (e.symm i)))
      (fun i => by simp)
  have H' : HasSum (fun n : ι →₀ ℕ => ∏ i, f i (n i))
      (∏ i : Fin (Fintype.card ι), a (e.symm i)) := by
    rw [hreindex]
    exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft e)).mpr H
  have hprodeq : (∏ i : Fin (Fintype.card ι), a (e.symm i)) = ∏ i, a i :=
    Fintype.prod_equiv e.symm (fun i => a (e.symm i)) a (fun i => by simp)
  rwa [hprodeq] at H'

/-- **The geometric-series specialization**: `Σ_{n : ι →₀ ℕ} ∏ᵢ qᵢ^{n(i)} = ∏ᵢ (1 - qᵢ)⁻¹`, given
`‖qᵢ‖ < 1` at every index. -/
theorem hasSum_prod_geometric {R : Type*} [NormedField R] [CompleteSpace R] {ι : Type*}
    [Fintype ι] (q : ι → R) (hq : ∀ i, ‖q i‖ < 1) :
    HasSum (fun n : ι →₀ ℕ => ∏ i, q i ^ n i) (∏ i, (1 - q i)⁻¹) :=
  hasSum_prod (fun i k => q i ^ k) (fun i => (1 - q i)⁻¹)
    (fun i => hasSum_geometric_of_norm_lt_one (hq i))
    (fun i => by
      simp only [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hq i))

end General

end Finsupp

import LeanCondensedMatter.SecondQuantization.Bosonic.BoltzmannWeightFactorization
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# The multi-mode free Boltzmann weight is summable, with total weight `∏ᵢ (1 - e^{-βεᵢ})⁻¹`

Phase B3c of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the genuine
(uncutoff) infinite sum `Σ_n e^{-βE(n)}` over *all* of `Occupation Mode`, for a finite mode set,
converges to the product of one-mode geometric series from `FreePartitionFunction.lean` whenever
every mode satisfies the one-mode convergence condition `0 < βεᵢ`. This is the multi-mode
generalization `BoltzmannWeightFactorization.lean` flagged as remaining.

The proof splits off one mode at a time by induction on `k` for `Mode := Fin k`, using
`Finsupp.optionEquiv : (Option α →₀ M) ≃ M × (α →₀ M)` to identify `Occupation (Option (Fin k)) ≃
ℕ × Occupation (Fin k)`, `HasSum.mul` to combine the one-mode and `k`-mode `HasSum` facts, and
`Equiv.hasSum_iff` to transport `HasSum` facts along the reindexing equivalences.
-/

namespace SecondQuantization
namespace Bosonic

/-! ## Reindexing `freeEigenvalue`/`boltzmannWeight` along an equivalence of mode sets -/

theorem freeEigenvalue_equivMapDomain {Mode Mode' : Type*} (e : Mode ≃ Mode') (ε : Mode' → ℝ)
    (n : Occupation Mode) :
    freeEigenvalue (ε ∘ e) n = freeEigenvalue ε (Finsupp.equivMapDomain e n) := by
  rw [freeEigenvalue, freeEigenvalue, Finsupp.sum_equivMapDomain]
  simp [Function.comp_apply]

theorem boltzmannWeight_equivMapDomain {Mode Mode' : Type*} (e : Mode ≃ Mode') (ε : Mode' → ℝ)
    (β : ℝ) (n : Occupation Mode) :
    boltzmannWeight (ε ∘ e) β n = boltzmannWeight ε β (Finsupp.equivMapDomain e n) := by
  rw [boltzmannWeight, boltzmannWeight, freeEigenvalue_equivMapDomain]

/-! ## Splitting off one mode via `Finsupp.optionEquiv` -/

theorem boltzmannWeight_option {A : Type*} (ε : Option A → ℝ) (β : ℝ) (m : Occupation (Option A)) :
    boltzmannWeight ε β m =
      oneModeBoltzmannWeight β (ε none) (Finsupp.optionEquiv m).1 *
        boltzmannWeight (ε ∘ Option.some) β (Finsupp.optionEquiv m).2 := by
  unfold boltzmannWeight oneModeBoltzmannWeight
  rw [← Real.exp_add]
  congr 1
  have hsplit : freeEigenvalue ε m =
      (m none : ℝ) * ε none + freeEigenvalue (ε ∘ Option.some) m.some := by
    rw [freeEigenvalue, freeEigenvalue,
      Finsupp.sum_option_index (h_zero := fun o => by ring)
        (h_add := fun o m₁ m₂ => by push_cast; ring)]
    rfl
  simp only [Finsupp.optionEquiv_apply]
  rw [hsplit]
  ring

/-! ## Nonnegative summability facts, in norm form -/

theorem summable_norm_of_nonneg {ι : Type*} {f : ι → ℝ} (hf : Summable f)
    (hpos : ∀ i, 0 ≤ f i) : Summable (fun i => ‖f i‖) := by
  rw [show (fun i => ‖f i‖) = f from funext fun i => Real.norm_of_nonneg (hpos i)]
  exact hf

/-! ## The `Fin`-indexed induction -/

/-- The genuine (uncutoff) sum over `Occupation (Fin k)` converges, given every mode's convergence
condition, to the product of one-mode geometric series. -/
theorem hasSum_boltzmannWeight_fin (k : ℕ) (ε : Fin k → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    HasSum (boltzmannWeight ε β) (∏ i, (1 - Real.exp (-β * ε i))⁻¹) := by
  induction k with
  | zero =>
    have hzero : ∀ n : Occupation (Fin 0), n = 0 := fun n => by ext i; exact i.elim0
    have hval : boltzmannWeight ε β (0 : Occupation (Fin 0)) = 1 := by
      simp [boltzmannWeight, freeEigenvalue]
    have hsum : HasSum (boltzmannWeight ε β) (boltzmannWeight ε β 0) :=
      hasSum_single (0 : Occupation (Fin 0)) (fun n' hn' => absurd (hzero n') hn')
    rw [hval] at hsum
    simpa using hsum
  | succ k ih =>
    set ε' : Fin k → ℝ := fun i => ε i.succ with hε'def
    have hpos' : ∀ i, 0 < β * ε' i := fun i => hpos i.succ
    have H2 : HasSum (boltzmannWeight ε' β) (∏ i, (1 - Real.exp (-β * ε' i))⁻¹) := ih ε' hpos'
    set εOpt : Option (Fin k) → ℝ := fun o => o.elim (ε 0) ε' with hεOptdef
    have hεOptnone : εOpt none = ε 0 := rfl
    have hεOptsome : εOpt ∘ Option.some = ε' := rfl
    have hsum0 : 0 < β * ε 0 := hpos 0
    have H1 : HasSum (oneModeBoltzmannWeight β (ε 0)) (1 - Real.exp (-β * ε 0))⁻¹ :=
      hasSum_oneModeBoltzmannWeight hsum0
    have hnn1 : ∀ x : ℕ, 0 ≤ oneModeBoltzmannWeight β (ε 0) x := fun x => Real.exp_nonneg _
    have hnn2 : ∀ n : Occupation (Fin k), 0 ≤ boltzmannWeight ε' β n := fun n => Real.exp_nonneg _
    have hmulsummable : Summable
        (fun p : ℕ × Occupation (Fin k) =>
          oneModeBoltzmannWeight β (ε 0) p.1 * boltzmannWeight ε' β p.2) :=
      summable_mul_of_summable_norm
        (summable_norm_of_nonneg H1.summable hnn1) (summable_norm_of_nonneg H2.summable hnn2)
    have H3 : HasSum
        (fun p : ℕ × Occupation (Fin k) =>
          oneModeBoltzmannWeight β (ε 0) p.1 * boltzmannWeight ε' β p.2)
        ((1 - Real.exp (-β * ε 0))⁻¹ * ∏ i, (1 - Real.exp (-β * ε' i))⁻¹) :=
      H1.mul H2 hmulsummable
    have hoption : boltzmannWeight εOpt β =
        (fun p : ℕ × Occupation (Fin k) =>
          oneModeBoltzmannWeight β (ε 0) p.1 * boltzmannWeight ε' β p.2) ∘ Finsupp.optionEquiv := by
      funext m
      rw [boltzmannWeight_option εOpt β m, hεOptnone, hεOptsome]
      rfl
    have H4 : HasSum (boltzmannWeight εOpt β)
        ((1 - Real.exp (-β * ε 0))⁻¹ * ∏ i, (1 - Real.exp (-β * ε' i))⁻¹) := by
      rw [hoption]
      exact (Equiv.hasSum_iff Finsupp.optionEquiv).mpr H3
    have hcomp : εOpt ∘ finSuccEquiv k = ε := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [εOpt, finSuccEquiv_zero]
      · intro j
        simp [εOpt, finSuccEquiv_succ, hε'def]
    have hreindex : boltzmannWeight ε β =
        boltzmannWeight εOpt β ∘ Finsupp.equivMapDomain (finSuccEquiv k) := by
      funext n
      conv_lhs => rw [← hcomp]
      exact boltzmannWeight_equivMapDomain (finSuccEquiv k) εOpt β n
    have H5 : HasSum (boltzmannWeight ε β)
        ((1 - Real.exp (-β * ε 0))⁻¹ * ∏ i, (1 - Real.exp (-β * ε' i))⁻¹) := by
      rw [hreindex]
      exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft (finSuccEquiv k))).mpr H4
    rw [Fin.prod_univ_succ]
    exact H5

theorem summable_boltzmannWeight_fin (k : ℕ) (ε : Fin k → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    Summable (boltzmannWeight ε β) :=
  (hasSum_boltzmannWeight_fin k ε β hpos).summable

theorem tsum_boltzmannWeight_fin (k : ℕ) (ε : Fin k → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    ∑' n, boltzmannWeight ε β n = ∏ i, (1 - Real.exp (-β * ε i))⁻¹ :=
  (hasSum_boltzmannWeight_fin k ε β hpos).tsum_eq

/-! ## The general finite `Mode` case, via `Fintype.equivFin` -/

/-- **The genuine (uncutoff) multi-mode free Boltzmann weight is summable**, converging to the
product of one-mode geometric series, given every mode's one-mode convergence condition
`0 < βεᵢ`. -/
theorem hasSum_boltzmannWeight {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ)
    (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    HasSum (boltzmannWeight ε β) (∏ i, (1 - Real.exp (-β * ε i))⁻¹) := by
  set e : Mode ≃ Fin (Fintype.card Mode) := Fintype.equivFin Mode with hedef
  have hcomp : (ε ∘ ⇑e.symm) ∘ ⇑e = ε := by
    funext i; simp
  have hpos' : ∀ i, 0 < β * (ε ∘ e.symm) i := fun i => by
    have := hpos (e.symm i)
    simpa using this
  have H := hasSum_boltzmannWeight_fin (Fintype.card Mode) (ε ∘ e.symm) β hpos'
  have hreindex :
      boltzmannWeight ε β = boltzmannWeight (ε ∘ e.symm) β ∘ Finsupp.equivMapDomain e := by
    funext n
    change boltzmannWeight ε β n = boltzmannWeight (ε ∘ e.symm) β (Finsupp.equivMapDomain e n)
    conv_lhs => rw [← hcomp]
    exact boltzmannWeight_equivMapDomain e (ε ∘ e.symm) β n
  have H' : HasSum (boltzmannWeight ε β) (∏ i : Fin (Fintype.card Mode),
      (1 - Real.exp (-β * (ε ∘ e.symm) i))⁻¹) := by
    rw [hreindex]
    exact (Equiv.hasSum_iff (Finsupp.equivCongrLeft e)).mpr H
  have hprodeq : (∏ i : Fin (Fintype.card Mode), (1 - Real.exp (-β * (ε ∘ e.symm) i))⁻¹) =
      ∏ i, (1 - Real.exp (-β * ε i))⁻¹ :=
    Fintype.prod_equiv e.symm (fun i => (1 - Real.exp (-β * (ε ∘ e.symm) i))⁻¹)
      (fun i => (1 - Real.exp (-β * ε i))⁻¹) (fun i => by simp)
  rw [hprodeq] at H'
  exact H'

theorem summable_boltzmannWeight {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ)
    (β : ℝ) (hpos : ∀ i, 0 < β * ε i) : Summable (boltzmannWeight ε β) :=
  (hasSum_boltzmannWeight ε β hpos).summable

theorem tsum_boltzmannWeight {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ)
    (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    ∑' n, boltzmannWeight ε β n = ∏ i, (1 - Real.exp (-β * ε i))⁻¹ :=
  (hasSum_boltzmannWeight ε β hpos).tsum_eq

end Bosonic
end SecondQuantization

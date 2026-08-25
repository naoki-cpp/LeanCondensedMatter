import LeanCondensedMatter.Analysis.OrderedSimplex.BinaryShuffle
import LeanCondensedMatter.Analysis.OrderedSimplex.BinaryShuffleIntegrand
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableIntegralBound
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityCast
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv

set_option linter.style.header false

/-!
# Ambient-slot binary-shuffle ordered-simplex integrals

A recursive `BinaryShuffle` already carries an order-preserving equivalence from its two local slot
families to the ambient slots. Using the generic ambient-slot integrand from the ordered-simplex
analysis layer, this module proves that its ordinary ordered-simplex integral is the recursive
contribution attached to the shuffle, and then transports the binary shuffle product identity to
the ambient `SlotShuffle` presentation.
-/

namespace Combinatorics
namespace BinaryShuffle

open intervalIntegral MeasureTheory

/-- One recursive shuffle contribution is the ordinary ordered-simplex integral of its ambient-slot
shuffled product. -/
theorem orderedSimplexContribution_eq_orderedSimplexIntegral_integrand :
    ∀ {m n : ℕ} (σ : BinaryShuffle m n) (β : ℝ)
      (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ),
      orderedSimplexContribution σ β f g =
        orderedSimplexIntegral (m + n) β ((toSlotShuffle σ).integrand f g)
  | 0, 0, .nil, _β, _f, _g => rfl
  | m + 1, n, .consLeft σ, β, f, g => by
      rw [orderedSimplexContribution]
      rw [intervalIntegral.orderedSimplexIntegral_cast
        (show m + 1 + n = (m + n) + 1 by lia)]
      rw [orderedSimplexIntegral_succ]
      apply intervalIntegral.integral_congr
      intro t _ht
      change orderedSimplexContribution σ t (fun rest => f (Fin.cons t rest)) g = _
      rw [orderedSimplexContribution_eq_orderedSimplexIntegral_integrand σ t
        (fun rest => f (Fin.cons t rest)) g]
      apply orderedSimplexIntegral_congr
      intro rest
      unfold SlotShuffle.integrand
      apply congrArg₂ (· * ·)
      · apply congrArg f
        funext i
        induction i using Fin.cases with
        | zero => simp [toSlotShuffle]
        | succ i => simp [toSlotShuffle]
      · apply congrArg g
        funext j
        simp [toSlotShuffle]
  | m, n + 1, .consRight σ, β, f, g => by
      rw [orderedSimplexContribution]
      rw [intervalIntegral.orderedSimplexIntegral_cast
        (show m + (n + 1) = (m + n) + 1 by lia)]
      rw [orderedSimplexIntegral_succ]
      apply intervalIntegral.integral_congr
      intro t _ht
      change orderedSimplexContribution σ t f (fun rest => g (Fin.cons t rest)) = _
      rw [orderedSimplexContribution_eq_orderedSimplexIntegral_integrand σ t f
        (fun rest => g (Fin.cons t rest))]
      apply orderedSimplexIntegral_congr
      intro rest
      unfold SlotShuffle.integrand
      apply congrArg₂ (· * ·)
      · apply congrArg f
        funext i
        simp [toSlotShuffle]
      · apply congrArg g
        funext j
        induction j using Fin.cases with
        | zero => simp [toSlotShuffle]
        | succ j => simp [toSlotShuffle]

/-- The inner integrand exposed by a left outer shuffle step is the ordered-simplex boundary of the
fixed ambient shuffled product. -/
theorem orderedSimplexContribution_consLeft_boundary {m n : ℕ}
    (σ : BinaryShuffle m n) (t : ℝ)
    (f : (Fin (m + 1) → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ) :
    orderedSimplexContribution σ t (fun rest => f (Fin.cons t rest)) g =
      orderedSimplexIntegral (m + n) t (fun rest =>
        (toSlotShuffle (.consLeft σ)).integrand f g
          (fun i : Fin (m + 1 + n) =>
            (Fin.cons t rest : Fin ((m + n) + 1) → ℝ)
              (Fin.cast (show m + 1 + n = (m + n) + 1 by lia) i))) := by
  rw [orderedSimplexContribution_eq_orderedSimplexIntegral_integrand]
  apply orderedSimplexIntegral_congr
  intro rest
  unfold SlotShuffle.integrand
  apply congrArg₂ (· * ·)
  · apply congrArg f
    funext i
    induction i using Fin.cases with
    | zero => simp [toSlotShuffle]
    | succ i => simp [toSlotShuffle]
  · apply congrArg g
    funext j
    simp [toSlotShuffle]

/-- The inner integrand exposed by a right outer shuffle step is the ordered-simplex boundary of the
fixed ambient shuffled product. -/
theorem orderedSimplexContribution_consRight_boundary {m n : ℕ}
    (σ : BinaryShuffle m n) (t : ℝ)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin (n + 1) → ℝ) → ℂ) :
    orderedSimplexContribution σ t f (fun rest => g (Fin.cons t rest)) =
      orderedSimplexIntegral (m + n) t (fun rest =>
        (toSlotShuffle (.consRight σ)).integrand f g
          (fun i : Fin (m + (n + 1)) =>
            (Fin.cons t rest : Fin ((m + n) + 1) → ℝ)
              (Fin.cast (show m + (n + 1) = (m + n) + 1 by lia) i))) := by
  rw [orderedSimplexContribution_eq_orderedSimplexIntegral_integrand]
  apply orderedSimplexIntegral_congr
  intro rest
  unfold SlotShuffle.integrand
  apply congrArg₂ (· * ·)
  · apply congrArg f
    funext i
    simp [toSlotShuffle]
  · apply congrArg g
    funext j
    induction j using Fin.cases with
    | zero => simp [toSlotShuffle]
    | succ j => simp [toSlotShuffle]

/-- The inner contribution at a left recursive shuffle step is interval integrable under measurable
local boundedness. -/
theorem intervalIntegrable_orderedSimplexContribution_consLeft {m n : ℕ}
    (σ : BinaryShuffle m n) (β : ℝ)
    (f : (Fin (m + 1) → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    IntervalIntegrable
      (fun t => orderedSimplexContribution σ t (fun rest => f (Fin.cons t rest)) g)
      volume 0 β := by
  let hdim : m + 1 + n = (m + n) + 1 := by lia
  let F : (Fin ((m + n) + 1) → ℝ) → ℂ := fun τ =>
    (toSlotShuffle (.consLeft σ)).integrand f g
      (fun i => τ (Fin.cast hdim i))
  have hF : MeasurableLocallyBounded F := by
    exact ((toSlotShuffle (.consLeft σ)).measurableLocallyBounded_integrand f g hf hg).finCast hdim
  have hInt := hF.intervalIntegrable_orderedSimplexIntegral_boundary β
  simpa only [F, hdim, orderedSimplexContribution_consLeft_boundary] using hInt

/-- The inner contribution at a right recursive shuffle step is interval integrable under measurable
local boundedness. -/
theorem intervalIntegrable_orderedSimplexContribution_consRight {m n : ℕ}
    (σ : BinaryShuffle m n) (β : ℝ)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin (n + 1) → ℝ) → ℂ)
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    IntervalIntegrable
      (fun t => orderedSimplexContribution σ t f (fun rest => g (Fin.cons t rest)))
      volume 0 β := by
  let hdim : m + (n + 1) = (m + n) + 1 := by lia
  let F : (Fin ((m + n) + 1) → ℝ) → ℂ := fun τ =>
    (toSlotShuffle (.consRight σ)).integrand f g
      (fun i => τ (Fin.cast hdim i))
  have hF : MeasurableLocallyBounded F := by
    exact ((toSlotShuffle (.consRight σ)).measurableLocallyBounded_integrand f g hf hg).finCast hdim
  have hInt := hF.intervalIntegrable_orderedSimplexIntegral_boundary β
  simpa only [F, hdim, orderedSimplexContribution_consRight_boundary] using hInt

/-- The finite sum of explicit binary-shuffle contributions is the recursive shuffle integral under
measurable local boundedness. -/
theorem sum_orderedSimplexContribution_eq_shuffleIntegral_of_measurableLocallyBounded :
    ∀ (m n : ℕ) (β : ℝ) (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ),
      MeasurableLocallyBounded f → MeasurableLocallyBounded g →
      (∑ σ : BinaryShuffle m n, orderedSimplexContribution σ β f g) =
        orderedSimplexShuffleIntegral m n β f g
  | 0, n, β, f, g, _hf, _hg => by
      rw [sum_zero_left, orderedSimplexContribution_allRight, orderedSimplexShuffleIntegral]
  | m + 1, 0, β, f, g, _hf, _hg => by
      rw [sum_zero_right, orderedSimplexContribution_allLeft, orderedSimplexShuffleIntegral]
  | m + 1, n + 1, β, f, g, hf, hg => by
      rw [sum_succ_succ]
      simp_rw [orderedSimplexContribution]
      rw [orderedSimplexShuffleIntegral]
      have hleft : ∀ t : ℝ,
          (∑ σ : BinaryShuffle m (n + 1),
            orderedSimplexContribution σ t (fun rest => f (Fin.cons t rest)) g) =
            orderedSimplexShuffleIntegral m (n + 1) t
              (fun rest => f (Fin.cons t rest)) g := by
        intro t
        exact sum_orderedSimplexContribution_eq_shuffleIntegral_of_measurableLocallyBounded
          m (n + 1) t (fun rest => f (Fin.cons t rest)) g (hf.finCons t) hg
      have hright : ∀ t : ℝ,
          (∑ σ : BinaryShuffle (m + 1) n,
            orderedSimplexContribution σ t f (fun rest => g (Fin.cons t rest))) =
            orderedSimplexShuffleIntegral (m + 1) n t f
              (fun rest => g (Fin.cons t rest)) := by
        intro t
        exact sum_orderedSimplexContribution_eq_shuffleIntegral_of_measurableLocallyBounded
          (m + 1) n t f (fun rest => g (Fin.cons t rest)) hf (hg.finCons t)
      have hIntLeft : ∀ σ : BinaryShuffle m (n + 1), IntervalIntegrable (fun t : ℝ =>
          orderedSimplexContribution σ t (fun rest => f (Fin.cons t rest)) g) volume 0 β := by
        intro σ
        exact intervalIntegrable_orderedSimplexContribution_consLeft σ β f g hf hg
      have hIntRight : ∀ σ : BinaryShuffle (m + 1) n, IntervalIntegrable (fun t : ℝ =>
          orderedSimplexContribution σ t f (fun rest => g (Fin.cons t rest))) volume 0 β := by
        intro σ
        exact intervalIntegrable_orderedSimplexContribution_consRight σ β f g hf hg
      simp_rw [← hleft, ← hright]
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_finsetSum, intervalIntegral.integral_finsetSum]
        · intro σ _
          exact hIntRight σ
        · intro σ _
          exact hIntLeft σ
      · simpa only [Finset.sum_fn] using
          (IntervalIntegrable.sum Finset.univ (fun σ _ => hIntLeft σ))
      · simpa only [Finset.sum_fn] using
          (IntervalIntegrable.sum Finset.univ (fun σ _ => hIntRight σ))

/-- Explicit binary ordered-simplex shuffle identity under measurable local boundedness. -/
theorem sum_orderedSimplexContribution_eq_mul_of_measurableLocallyBounded
    (m n : ℕ) (β : ℝ)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    (∑ σ : BinaryShuffle m n, orderedSimplexContribution σ β f g) =
      orderedSimplexIntegral m β f * orderedSimplexIntegral n β g := by
  rw [sum_orderedSimplexContribution_eq_shuffleIntegral_of_measurableLocallyBounded
    m n β f g hf hg]
  exact orderedSimplexShuffleIntegral_eq_mul_of_measurableLocallyBounded m n β f g hf hg

/-- Ambient-slot form of the explicit binary ordered-simplex shuffle identity under measurable local
boundedness. -/
theorem sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
    (m n : ℕ) (β : ℝ)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : MeasurableLocallyBounded f) (hg : MeasurableLocallyBounded g) :
    (∑ shuffle : SlotShuffle m n,
      orderedSimplexIntegral (m + n) β (shuffle.integrand f g)) =
      orderedSimplexIntegral m β f * orderedSimplexIntegral n β g := by
  rw [sum_slotShuffle]
  simp_rw [← orderedSimplexContribution_eq_orderedSimplexIntegral_integrand]
  exact sum_orderedSimplexContribution_eq_mul_of_measurableLocallyBounded m n β f g hf hg

/-- Ambient-slot form of the explicit binary ordered-simplex shuffle identity. -/
theorem sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul (m n : ℕ) (β : ℝ)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    (∑ shuffle : SlotShuffle m n,
      orderedSimplexIntegral (m + n) β (shuffle.integrand f g)) =
      orderedSimplexIntegral m β f * orderedSimplexIntegral n β g := by
  rw [sum_slotShuffle]
  simp_rw [← orderedSimplexContribution_eq_orderedSimplexIntegral_integrand]
  exact sum_orderedSimplexContribution_eq_mul m n β f g hf hg

end BinaryShuffle
end Combinatorics

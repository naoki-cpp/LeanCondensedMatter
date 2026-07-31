import LeanCondensedMatter.Analysis.OrderedSimplex.BinaryShuffle
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv

set_option linter.style.header false

/-!
# Ambient-slot binary-shuffle ordered-simplex integrals

A recursive `BinaryShuffle` already carries an order-preserving equivalence from its two local slot
families to the ambient slots. This module evaluates two local integrands through that equivalence,
proves that the resulting ordinary ordered-simplex integral is the recursive contribution attached
to the shuffle, and then transports the binary shuffle product identity to the ambient
`SlotShuffle` presentation.
-/

namespace Combinatorics
namespace BinaryShuffle

open intervalIntegral

/-- Product of two local integrands after their coordinates are embedded by an ambient slot
shuffle. -/
noncomputable def SlotShuffle.integrand {m n : ℕ} (shuffle : SlotShuffle m n)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (τ : Fin (m + n) → ℝ) : ℂ :=
  f (fun i => τ (shuffle.slotEquiv (Sum.inl i))) *
    g (fun j => τ (shuffle.slotEquiv (Sum.inr j)))

/-- The ambient shuffled product is continuous when both local integrands are continuous. -/
theorem SlotShuffle.continuous_integrand {m n : ℕ} (shuffle : SlotShuffle m n)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (shuffle.integrand f g) := by
  have hleft : Continuous (fun τ : Fin (m + n) → ℝ =>
      fun i : Fin m => τ (shuffle.slotEquiv (Sum.inl i))) :=
    continuous_pi fun i => continuous_apply (shuffle.slotEquiv (Sum.inl i))
  have hright : Continuous (fun τ : Fin (m + n) → ℝ =>
      fun j : Fin n => τ (shuffle.slotEquiv (Sum.inr j))) :=
    continuous_pi fun j => continuous_apply (shuffle.slotEquiv (Sum.inr j))
  exact (hf.comp hleft).mul (hg.comp hright)

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
        (show m + 1 + n = (m + n) + 1 by omega)]
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
        (show m + (n + 1) = (m + n) + 1 by omega)]
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

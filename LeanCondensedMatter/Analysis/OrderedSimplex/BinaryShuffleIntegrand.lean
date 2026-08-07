import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.Combinatorics.BinaryShuffleSlots
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Integrands associated with ambient binary slot shuffles

This module evaluates two local complex-valued integrands after their coordinates are embedded by an
order-preserving ambient `BinaryShuffle.SlotShuffle`.  It belongs to the ordered-simplex analysis
layer rather than the pure combinatorics layer.
-/

namespace Combinatorics
namespace BinaryShuffle

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

/-- Measurable local boundedness is preserved by an ambient binary slot shuffle. -/
theorem SlotShuffle.measurableLocallyBounded_integrand {m n : ℕ}
    (shuffle : SlotShuffle m n)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : intervalIntegral.MeasurableLocallyBounded f)
    (hg : intervalIntegral.MeasurableLocallyBounded g) :
    intervalIntegral.MeasurableLocallyBounded (shuffle.integrand f g) := by
  have hleft : Continuous (fun τ : Fin (m + n) → ℝ =>
      fun i : Fin m => τ (shuffle.slotEquiv (Sum.inl i))) :=
    continuous_pi fun i => continuous_apply (shuffle.slotEquiv (Sum.inl i))
  have hright : Continuous (fun τ : Fin (m + n) → ℝ =>
      fun j : Fin n => τ (shuffle.slotEquiv (Sum.inr j))) :=
    continuous_pi fun j => continuous_apply (shuffle.slotEquiv (Sum.inr j))
  refine ⟨(hf.1.comp hleft.measurable).mul (hg.1.comp hright.measurable), ?_⟩
  intro R hR
  obtain ⟨Cf, hCf0, hCf⟩ := hf.2 R hR
  obtain ⟨Cg, hCg0, hCg⟩ := hg.2 R hR
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, ?_⟩
  intro τ hτ
  have hleftMem : (fun i : Fin m => τ (shuffle.slotEquiv (Sum.inl i))) ∈
      intervalIntegral.orderedSimplexTimeCube m R := by
    rw [intervalIntegral.orderedSimplexTimeCube, Set.mem_Icc] at hτ ⊢
    exact ⟨fun i => hτ.1 (shuffle.slotEquiv (Sum.inl i)),
      fun i => hτ.2 (shuffle.slotEquiv (Sum.inl i))⟩
  have hrightMem : (fun j : Fin n => τ (shuffle.slotEquiv (Sum.inr j))) ∈
      intervalIntegral.orderedSimplexTimeCube n R := by
    rw [intervalIntegral.orderedSimplexTimeCube, Set.mem_Icc] at hτ ⊢
    exact ⟨fun j => hτ.1 (shuffle.slotEquiv (Sum.inr j)),
      fun j => hτ.2 (shuffle.slotEquiv (Sum.inr j))⟩
  rw [SlotShuffle.integrand, norm_mul]
  exact mul_le_mul (hCf _ hleftMem) (hCg _ hrightMem) (norm_nonneg _) hCf0

end BinaryShuffle
end Combinatorics
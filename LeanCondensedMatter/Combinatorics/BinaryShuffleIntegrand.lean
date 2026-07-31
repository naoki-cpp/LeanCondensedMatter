import LeanCondensedMatter.Combinatorics.BinaryShuffleSlots
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Integrands associated with ambient binary slot shuffles

This module evaluates two local complex-valued integrands after their coordinates are embedded by an
order-preserving ambient `BinaryShuffle.SlotShuffle`. The construction and its continuity theorem do
not depend on ordered-simplex integration.
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

end BinaryShuffle
end Combinatorics

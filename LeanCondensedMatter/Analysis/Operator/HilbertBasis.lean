module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum

public section

/-!
# Hilbert basis identities and extension

Extend an indexed orthonormal family to a Hilbert basis while retaining an injective
map of the original index type into the basis index type. The squared-coefficient
Parseval identity is expressed directly using Mathlib's `lp.hasSum_norm`.
-/

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- An indexed orthonormal family embeds into a Hilbert basis, preserving its vectors. -/
theorem exists_hilbertBasis_extension_injective {d : ι → E} (hd : Orthonormal 𝕜 d) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E) (e : ι → w),
      Function.Injective e ∧ ∀ i, b (e i) = d i := by
  obtain ⟨w, b, hsub, hb⟩ := hd.toSubtypeRange.exists_hilbertBasis_extension
  let e : ι → w := fun i => ⟨d i, hsub ⟨i, rfl⟩⟩
  refine ⟨w, b, e, ?_, ?_⟩
  · intro i j hij
    exact hd.linearIndependent.injective (congrArg Subtype.val hij)
  · intro i
    rw [hb]

end Orthonormal

namespace HilbertBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Parseval's identity for the squared norms of Hilbert-basis coefficients. -/
theorem hasSum_norm_sq_inner (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
    b.repr_apply_apply, b.repr.norm_map] using (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))

end HilbertBasis

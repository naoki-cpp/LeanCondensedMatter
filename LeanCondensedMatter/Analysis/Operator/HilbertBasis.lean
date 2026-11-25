module

public import Mathlib.Analysis.InnerProductSpace.l2Space

public section

/-!
# Hilbert basis extension

Extend an indexed orthonormal family to a Hilbert basis while retaining an injective
map of the original index type into the basis index type.
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

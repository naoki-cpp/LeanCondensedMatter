import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily

set_option linter.style.header false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

noncomputable def eigenvectorHilbertBasisMkSpike
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    HilbertBasis (EigenvectorIndex T) ℂ
      (Submodule.span ℂ (Set.range (eigenvectorFamily hT))).topologicalClosure := by
  set E' := Submodule.span ℂ (Set.range (eigenvectorFamily hT)) with hE'_def
  set F := E'.topologicalClosure with hF_def
  have hmem : ∀ a, eigenvectorFamily hT a ∈ F := fun a =>
    hF_def ▸ E'.le_topologicalClosure (hE'_def ▸ Submodule.subset_span ⟨a, rfl⟩)
  let v : EigenvectorIndex T → F :=
    fun a => ⟨eigenvectorFamily hT a, hmem a⟩
  have hv : Orthonormal ℂ v := by
    constructor
    · intro a
      simpa [v] using (orthonormal_eigenvectorFamily hT hT').1 a
    · intro a b hab
      simpa [v, Submodule.coe_inner] using
        (orthonormal_eigenvectorFamily hT hT').2 hab
  refine HilbertBasis.mk hv ?_
  rw [← eq_top_iff]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  rw [F.subtypeₗᵢ.isometry.isEmbedding.isInducing.dense_iff]
  intro y
  have hspaneq : Submodule.map F.subtypeₗᵢ.toLinearMap
      (Submodule.span ℂ (Set.range v)) = E' := by
    rw [Submodule.map_span, hE'_def]
    congr 1
    ext z
    constructor
    · rintro ⟨-, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  have himg : F.subtypeₗᵢ '' (Submodule.span ℂ (Set.range v) : Set F) =
      (E' : Set H) := by
    rw [← hspaneq]
    exact (Submodule.map_coe _ _).symm
  rw [himg, ← Submodule.topologicalClosure_coe, ← hF_def]
  exact y.2

example (hT : IsCompactOperator T) (hT' : T.IsSymmetric) (a : EigenvectorIndex T) :
    (eigenvectorHilbertBasisMkSpike hT hT' a : H) = eigenvectorFamily hT a := by
  simp [eigenvectorHilbertBasisMkSpike, HilbertBasis.coe_mk]

end ContinuousLinearMap

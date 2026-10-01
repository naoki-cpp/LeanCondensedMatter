import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option linter.style.header false

/-!
# Complex eigenvector families for compact operators

This module packages the nonzero complex eigenspaces of a compact operator into one indexed family.
Compactness makes every nonzero eigenspace finite-dimensional. No symmetry, self-adjointness, or
normality hypothesis is required for the definitions and algebraic span results in this module.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The index type formed from every nonzero complex eigenvalue of `T` and a basis index in its
finite-dimensional eigenspace. -/
def ComplexEigenvectorIndex (T : H →L[ℂ] H) : Type :=
  Σ λ : { λ : ℂ // λ ≠ 0 },
    Fin (Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1))

/-- Every nonzero complex eigenspace of a compact operator is finite-dimensional. -/
theorem finiteDimensional_complexEigenspace_ne_zero (hT : IsCompactOperator T)
    (λ : { λ : ℂ // λ ≠ 0 }) :
    FiniteDimensional ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1) :=
  finite_dimensional_eigenspace hT λ.1 λ.2

/-- A chosen basis vector from each nonzero complex eigenspace of a compact operator. -/
noncomputable def complexEigenvectorFamily (hT : IsCompactOperator T) :
    ComplexEigenvectorIndex T → H :=
  fun a =>
    haveI := finiteDimensional_complexEigenspace_ne_zero hT a.1
    ((Module.finBasis ℂ
      (Module.End.eigenspace (T : H →ₗ[ℂ] H) a.1.1)) a.2 : H)

/-- Each vector in `complexEigenvectorFamily` is an eigenvector with the eigenvalue stored in its
index. -/
theorem apply_complexEigenvectorFamily (hT : IsCompactOperator T) (a : ComplexEigenvectorIndex T) :
    (T : H →ₗ[ℂ] H) (complexEigenvectorFamily hT a) =
      a.1.1 • complexEigenvectorFamily hT a := by
  apply Module.End.mem_eigenspace_iff.mp
  haveI := finiteDimensional_complexEigenspace_ne_zero hT a.1
  exact Submodule.coe_mem _

/-- The span of `complexEigenvectorFamily` is the sum of all nonzero complex eigenspaces. -/
theorem span_complexEigenvectorFamily (hT : IsCompactOperator T) :
    Submodule.span ℂ (Set.range (complexEigenvectorFamily hT)) =
      ⨆ λ : { λ : ℂ // λ ≠ 0 },
        Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨a, rfl⟩
    exact Submodule.mem_iSup_of_mem a.1 (by
      haveI := finiteDimensional_complexEigenspace_ne_zero hT a.1
      exact Submodule.coe_mem _)
  · apply iSup_le
    intro λ
    haveI := finiteDimensional_complexEigenspace_ne_zero hT λ
    have hbasis : Submodule.span ℂ
        (Set.range (Module.finBasis ℂ
          (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1))) =
        (⊤ : Submodule ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1)) :=
      (Module.finBasis ℂ
        (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1)).span_eq
    have hmap : Submodule.map
        (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1).subtype
        (Submodule.span ℂ
          (Set.range (Module.finBasis ℂ
            (Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1)))) =
        Module.End.eigenspace (T : H →ₗ[ℂ] H) λ.1 := by
      rw [hbasis, Submodule.map_top, Submodule.range_subtype]
    rw [← hmap, Submodule.map_span]
    apply Submodule.span_mono
    rintro x ⟨v, ⟨y, rfl⟩, rfl⟩
    exact ⟨⟨λ, y⟩, rfl⟩

end ContinuousLinearMap

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A countable orthonormal family of eigenvectors for a compact self-adjoint operator

Mathlib's spectral theorem for compact self-adjoint operators (`Mathlib.Analysis.
InnerProductSpace.Spectrum`) only proves qualitative facts about eigenspaces as submodules
(`orthogonalComplement_iSup_eigenspaces_eq_bot`, `finite_dimensional_eigenspace`) — it never
packages these into an actual countable indexed orthonormal family of eigenvectors. This file
takes the first step towards Track C's trace-class operator theory
(`notes/roadmaps/operator-algebra.md`) by building that family, gluing together an orthonormal
basis of each nonzero eigenspace via `OrthogonalFamily.orthonormal_sigma_orthonormal`.

**Scope note:** the eigenvalue-`0` eigenspace (the kernel of `T`) is deliberately excluded from
the family — it contributes nothing to the trace regardless of its (possibly infinite, even
non-separable) dimension, so restricting to nonzero eigenvalues keeps the index type free of
that complication. See `notes/caveats.md` for what remains: countability of the index type
(from compactness) and the `tsum` reconstruction of `T` from this family, neither proved here.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The index type gluing together an orthonormal basis of each nonzero eigenspace of `T`: a
nonzero real eigenvalue `μ`, together with an index into a chosen orthonormal basis of the
(finite-dimensional, for `μ ≠ 0`) eigenspace `eigenspace T μ`. -/
def EigenvectorIndex (T : H →L[ℂ] H) : Type :=
  Σ μ : { μ : ℝ // μ ≠ 0 }, Fin (Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)))

/-- The orthonormal family of eigenvectors of `T`, glued from an orthonormal basis of each
nonzero eigenspace. -/
noncomputable def eigenvectorFamily (hT : IsCompactOperator T) :
    EigenvectorIndex T → H :=
  fun a =>
    haveI := finite_dimensional_eigenspace hT (a.1.1 : ℂ) (by exact_mod_cast a.1.2)
    ((stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ))) a.2 : H)

theorem orthonormal_eigenvectorFamily (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    Orthonormal ℂ (eigenvectorFamily hT) := by
  have hOrth : OrthogonalFamily ℂ (fun μ : ℝ => Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ : ℂ))
      (fun μ => (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ : ℂ)).subtypeₗᵢ) :=
    hT'.orthogonalFamily_eigenspaces.comp
      (f := fun μ : ℝ => (μ : ℂ)) (Complex.ofReal_injective)
  have hOrth' : OrthogonalFamily ℂ
      (fun μ : { μ : ℝ // μ ≠ 0 } => Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))
      (fun μ => (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)).subtypeₗᵢ) :=
    hOrth.comp (f := fun μ : { μ : ℝ // μ ≠ 0 } => μ.1) Subtype.val_injective
  have := hOrth'.orthonormal_sigma_orthonormal
    (v_family := fun μ : { μ : ℝ // μ ≠ 0 } =>
      haveI := finite_dimensional_eigenspace hT (μ.1 : ℂ) (by exact_mod_cast μ.2)
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)) : _ → _))
    (fun μ =>
      haveI := finite_dimensional_eigenspace hT (μ.1 : ℂ) (by exact_mod_cast μ.2)
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))).orthonormal)
  exact this

end ContinuousLinearMap

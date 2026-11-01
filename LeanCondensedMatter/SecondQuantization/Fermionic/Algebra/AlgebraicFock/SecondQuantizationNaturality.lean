import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity
import Mathlib.Algebra.Algebra.Equiv

set_option linter.style.header false

/-!
# Linear changes of one-particle coordinates and fermionic second quantization

Mathlib's `ExteriorAlgebra.map` lifts a one-particle linear map to the algebraic Fock space.
It intertwines second-quantized operators whenever the original map intertwines the one-particle
operators. For a linear equivalence this gives covariance under conjugation. These statements
are algebraic: they assert neither Hilbert-space unitarity nor covariance of thermal states.
-/

namespace SecondQuantization.Fermionic.AlgebraicFock

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A one-particle intertwiner lifts through the exterior algebra to an intertwiner of the
second-quantized operators, without finite-dimensionality or invertibility assumptions. -/
theorem map_dGamma (f : V →ₗ[ℂ] W) (T : V →ₗ[ℂ] V) (S : W →ₗ[ℂ] W)
    (h : ∀ v, f (T v) = S (f v)) (Ψ : AlgebraicFock V) :
    ExteriorAlgebra.map f (dGamma V T Ψ) = dGamma W S (ExteriorAlgebra.map f Ψ) := by
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
      change ExteriorAlgebra.map f (dGamma V T (oneParticle V v * x)) =
        dGamma W S (ExteriorAlgebra.map f (oneParticle V v * x))
      simp [dGamma_oneParticle_mul, oneParticle, h, hx]

/-- Changing one-particle coordinates before second quantization agrees with changing the
exterior-Fock coordinates after second quantization. The inverse maps are the existing
`ExteriorAlgebra.map` applied to the two directions of the linear equivalence. -/
theorem map_dGamma_conj (e : V ≃ₗ[ℂ] W) (T : V →ₗ[ℂ] V) (Ψ : AlgebraicFock W) :
    ExteriorAlgebra.map e.toLinearMap
        (dGamma V T (ExteriorAlgebra.map e.symm.toLinearMap Ψ)) =
      dGamma W (e.conjAlgEquiv ℂ T) Ψ := by
  have hcomp : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext w
    exact e.apply_symm_apply w
  have hcancel : ExteriorAlgebra.map e.toLinearMap
      (ExteriorAlgebra.map e.symm.toLinearMap Ψ) = Ψ := by
    have hmap := congrArg (fun F : AlgebraicFock W →ₐ[ℂ] AlgebraicFock W => F Ψ)
      (ExteriorAlgebra.map_comp_map e.symm.toLinearMap e.toLinearMap)
    simpa only [AlgHom.comp_apply, hcomp, ExteriorAlgebra.map_id, AlgHom.id_apply] using hmap
  have hintertwine (v : V) : e.toLinearMap (T v) = (e.conjAlgEquiv ℂ T) (e.toLinearMap v) := by
    change e (T v) = e (T (e.symm (e v)))
    rw [e.symm_apply_apply]
  have h := map_dGamma e.toLinearMap T (e.conjAlgEquiv ℂ T) hintertwine
    (ExteriorAlgebra.map e.symm.toLinearMap Ψ)
  rw [hcancel] at h
  exact h

end SecondQuantization.Fermionic.AlgebraicFock

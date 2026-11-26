import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.FiniteHilbertRealization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationNaturality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

set_option linter.style.header false

/-!
# Isometric exterior transport in finite occupation-Hilbert coordinates

The occupation-Hilbert inner product does not depend on the chosen orthonormal one-particle
basis. One-particle isometries preserve this inner product through the exterior lift; unitary
one-particle maps therefore give unitary maps between the finite occupation-Hilbert realizations.
No normed-space instance is imposed on the algebraic exterior algebra.
-/

namespace SecondQuantization.Fermionic.AlgebraicFock

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem finiteHilbertEquiv_one (b : Module.Basis Mode ℂ H) :
    finiteHilbertEquiv b 1 = Common.finiteHilbertBasisState (∅ : Occupation Mode) := by
  have hempty : b.ExteriorAlgebra (∅ : Occupation Mode) = (1 : AlgebraicFock H) := by
    rw [ExteriorAlgebra.basis_apply_ofCard (n := 0) b rfl]
    simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
  rw [← hempty, ← occupationEquiv_basisState]
  change Common.finiteHilbertFockEquiv
    ((occupationEquiv b).symm (occupationEquiv b
      (SecondQuantization.Fermionic.basisState (∅ : Occupation Mode)))) = _
  rw [LinearEquiv.symm_apply_apply]
  simpa only [SecondQuantization.Fermionic.basisState] using
    Common.finiteHilbertFockEquiv_basisState (∅ : Occupation Mode)

private theorem norm_finiteHilbertEquiv_one (b : Module.Basis Mode ℂ H) :
    ‖finiteHilbertEquiv b 1‖ = 1 := by
  rw [finiteHilbertEquiv_one]
  simpa only [Common.finiteHilbertOrthonormalBasis_apply] using
    (Common.finiteHilbertOrthonormalBasis (Config := Occupation Mode)).orthonormal.1
      (∅ : Occupation Mode)

private theorem inner_finiteHilbert_create (b : OrthonormalBasis Mode ℂ H)
    (v : H) (x y : AlgebraicFock H) :
    inner ℂ (finiteHilbertEquiv b.toBasis (create H v x)) (finiteHilbertEquiv b.toBasis y) =
      inner ℂ (finiteHilbertEquiv b.toBasis x)
        (finiteHilbertEquiv b.toBasis (annihilate H v y)) := by
  have h := (ContinuousLinearMap.adjoint_inner_right
    (finiteHilbertOperatorAlgEquiv b.toBasis (create H v))
    (finiteHilbertEquiv b.toBasis x) (finiteHilbertEquiv b.toBasis y)).symm
  change inner ℂ
      (finiteHilbertOperatorAlgEquiv b.toBasis (create H v) (finiteHilbertEquiv b.toBasis x))
      (finiteHilbertEquiv b.toBasis y) =
    inner ℂ (finiteHilbertEquiv b.toBasis x)
      (star (finiteHilbertOperatorAlgEquiv b.toBasis (create H v))
        (finiteHilbertEquiv b.toBasis y)) at h
  rw [star_finiteHilbertOperator_create, finiteHilbertOperator_apply,
    finiteHilbertOperator_apply] at h
  exact h

/-- The degree-one exterior embedding preserves the original Hilbert inner
product in any orthonormal coordinate basis. The proof is the vacuum
creation/annihilation identity, not a coordinate expansion. -/
theorem inner_finiteHilbertEquiv_oneParticle (b : OrthonormalBasis Mode ℂ H)
    (v w : H) :
    inner ℂ (finiteHilbertEquiv b.toBasis (oneParticle H v))
        (finiteHilbertEquiv b.toBasis (oneParticle H w)) = inner ℂ v w := by
  have hc : create H v (1 : AlgebraicFock H) = oneParticle H v := by
    rw [create_apply, mul_one]
  have hs : algebraMap ℂ (AlgebraicFock H) (inner ℂ v w) =
      inner ℂ v w • (1 : AlgebraicFock H) := by
    rw [Algebra.smul_def, mul_one]
  rw [← hc, inner_finiteHilbert_create, annihilate_oneParticle, hs,
    map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_finiteHilbertEquiv_one]
  simp

/-- Canonical isometric realization of the one-particle sector in finite Fock
space, expressed using an orthonormal basis of the one-particle Hilbert space. -/
def finiteHilbertOneParticleEmbedding (b : OrthonormalBasis Mode ℂ H) :
    H →ₗᵢ[ℂ] Common.FiniteHilbertFock (Occupation Mode) :=
  ((finiteHilbertEquiv b.toBasis).toLinearMap.comp (oneParticle H)).isometryOfInner
    (inner_finiteHilbertEquiv_oneParticle b)

@[simp]
theorem finiteHilbertOneParticleEmbedding_apply (b : OrthonormalBasis Mode ℂ H)
    (v : H) :
    finiteHilbertOneParticleEmbedding b v =
      finiteHilbertEquiv b.toBasis (oneParticle H v) := rfl

/-- Restriction of the bounded exterior second quantization to the isometric
one-particle sector is the original one-particle linear operator. -/
theorem finiteHilbertOperator_dGamma_apply_embedding (b : OrthonormalBasis Mode ℂ H)
    (T : H →ₗ[ℂ] H) (v : H) :
    finiteHilbertOperatorAlgEquiv b.toBasis (dGamma H T)
        (finiteHilbertOneParticleEmbedding b v) =
      finiteHilbertOneParticleEmbedding b (T v) := by
  simp only [finiteHilbertOneParticleEmbedding_apply, finiteHilbertOperator_dGamma_oneParticle]

/-- Exact one-particle matrix elements in the full bounded Fock representation. -/
theorem inner_finiteHilbertOperator_dGamma_embedding (b : OrthonormalBasis Mode ℂ H)
    (T : H →ₗ[ℂ] H) (v w : H) :
    inner ℂ (finiteHilbertOneParticleEmbedding b v)
        (finiteHilbertOperatorAlgEquiv b.toBasis (dGamma H T)
          (finiteHilbertOneParticleEmbedding b w)) = inner ℂ v (T w) := by
  rw [finiteHilbertOperator_dGamma_apply_embedding]
  exact (finiteHilbertOneParticleEmbedding b).inner_map_map v (T w)

variable {N : Type*} [LinearOrder N] [Fintype N]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The exterior lift of a one-particle isometry preserves the occupation-Hilbert inner product
in arbitrary finite orthonormal coordinate bases, which need not be carried into each other. -/
theorem inner_finiteHilbertEquiv_map (b : OrthonormalBasis Mode ℂ H)
    (c : OrthonormalBasis N ℂ K) (e : H →ₗᵢ[ℂ] K) (x y : AlgebraicFock H) :
    inner ℂ (finiteHilbertEquiv c.toBasis (ExteriorAlgebra.map e.toLinearMap x))
        (finiteHilbertEquiv c.toBasis (ExteriorAlgebra.map e.toLinearMap y)) =
      inner ℂ (finiteHilbertEquiv b.toBasis x) (finiteHilbertEquiv b.toBasis y) := by
  apply inner_realization_map_eq (finiteHilbertEquiv b.toBasis).toLinearMap
    (finiteHilbertEquiv c.toBasis).toLinearMap e
    (inner_finiteHilbert_create b) (inner_finiteHilbert_create c)
  change ‖finiteHilbertEquiv c.toBasis 1‖ = ‖finiteHilbertEquiv b.toBasis 1‖
  rw [norm_finiteHilbertEquiv_one, norm_finiteHilbertEquiv_one]

/-- The unitary exterior lift of a one-particle unitary, expressed in finite occupation-Hilbert
coordinates. The source and target orthonormal bases are arbitrary. -/
def finiteHilbertMap (b : OrthonormalBasis Mode ℂ H) (c : OrthonormalBasis N ℂ K)
    (e : H ≃ₗᵢ[ℂ] K) :
    Common.FiniteHilbertFock (Occupation Mode) ≃ₗᵢ[ℂ] Common.FiniteHilbertFock (Occupation N) := by
  let q : (0 : QuadraticForm ℂ H).IsometryEquiv (0 : QuadraticForm ℂ K) :=
    { e.toLinearEquiv with map_app' := fun _ => rfl }
  let E := (CliffordAlgebra.equivOfIsometry q).toLinearEquiv
  let F := (finiteHilbertEquiv b.toBasis).symm.trans (E.trans (finiteHilbertEquiv c.toBasis))
  refine F.isometryOfInner ?_
  intro x y
  change inner ℂ
      (finiteHilbertEquiv c.toBasis
        (ExteriorAlgebra.map e.toLinearIsometry.toLinearMap ((finiteHilbertEquiv b.toBasis).symm x)))
      (finiteHilbertEquiv c.toBasis
        (ExteriorAlgebra.map e.toLinearIsometry.toLinearMap ((finiteHilbertEquiv b.toBasis).symm y))) = _
  rw [inner_finiteHilbertEquiv_map b c e.toLinearIsometry]
  simp only [LinearEquiv.apply_symm_apply]

/-- The finite-Hilbert unitary is the exterior lift expressed in the chosen coordinates. -/
theorem finiteHilbertMap_apply (b : OrthonormalBasis Mode ℂ H)
    (c : OrthonormalBasis N ℂ K) (e : H ≃ₗᵢ[ℂ] K) (x : AlgebraicFock H) :
    finiteHilbertMap b c e (finiteHilbertEquiv b.toBasis x) =
      finiteHilbertEquiv c.toBasis (ExteriorAlgebra.map e.toLinearEquiv.toLinearMap x) := by
  change finiteHilbertEquiv c.toBasis
    (ExteriorAlgebra.map e.toLinearEquiv.toLinearMap
      ((finiteHilbertEquiv b.toBasis).symm (finiteHilbertEquiv b.toBasis x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The existing unitary exterior lift acts on arbitrary algebraic coordinates
when their one-particle embedding intertwines the supplied maps. No Hilbert
space structure on the algebraic coordinate space is required. -/
theorem finiteHilbertMap_apply_of_basis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b₀ : Module.Basis Mode ℂ V) (b : OrthonormalBasis Mode ℂ H)
    (j : V →ₗ[ℂ] H) (hj : ∀ i, j (b₀ i) = b i)
    (e : H ≃ₗᵢ[ℂ] H) (f : V →ₗ[ℂ] V)
    (hf : e.toLinearEquiv.toLinearMap.comp j = j.comp f) (x : AlgebraicFock V) :
    finiteHilbertMap b b e (finiteHilbertEquiv b₀ x) =
      finiteHilbertEquiv b₀ (ExteriorAlgebra.map f x) := by
  calc
    _ = finiteHilbertMap b b e
        (finiteHilbertEquiv b.toBasis (ExteriorAlgebra.map j x)) := by
          rw [finiteHilbertEquiv_map_of_basis b₀ b.toBasis j hj]
    _ = finiteHilbertEquiv b.toBasis
        (ExteriorAlgebra.map e.toLinearEquiv.toLinearMap (ExteriorAlgebra.map j x)) :=
          finiteHilbertMap_apply b b e _
    _ = finiteHilbertEquiv b.toBasis
        (ExteriorAlgebra.map j (ExteriorAlgebra.map f x)) := by
          have h := congrArg
            (fun L : V →ₗ[ℂ] H => finiteHilbertEquiv b.toBasis (ExteriorAlgebra.map L x)) hf
          rw [← ExteriorAlgebra.map_comp_map j e.toLinearEquiv.toLinearMap,
            ← ExteriorAlgebra.map_comp_map f j] at h
          simpa only [AlgHom.comp_apply] using h
    _ = _ := finiteHilbertEquiv_map_of_basis b₀ b.toBasis j hj _

/-- Conjugating a finite-Hilbert second quantization by the exterior unitary
implements the corresponding one-particle intertwiner in algebraic coordinates.
This keeps all Hilbert-space transports at the generic basis level. -/
theorem finiteHilbertMap_conj_dGamma_of_basis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b₀ : Module.Basis Mode ℂ V) (b : OrthonormalBasis Mode ℂ H)
    (j : V →ₗ[ℂ] H) (hj : ∀ i, j (b₀ i) = b i)
    (e : H ≃ₗᵢ[ℂ] H) (f : V →ₗ[ℂ] V)
    (hf : e.toLinearEquiv.toLinearMap.comp j = j.comp f)
    (T S : V →ₗ[ℂ] V) (hTS : ∀ v, f (T v) = S (f v)) :
    (finiteHilbertMap b b e).conjStarAlgEquiv
        (finiteHilbertOperatorAlgEquiv b₀ (dGamma V T)) =
      finiteHilbertOperatorAlgEquiv b₀ (dGamma V S) := by
  let W := finiteHilbertMap b b e
  change W.conjStarAlgEquiv (finiteHilbertOperatorAlgEquiv b₀ (dGamma V T)) =
    finiteHilbertOperatorAlgEquiv b₀ (dGamma V S)
  have hMap (v : AlgebraicFock V) :
      W (finiteHilbertEquiv b₀ v) = finiteHilbertEquiv b₀ (ExteriorAlgebra.map f v) :=
    finiteHilbertMap_apply_of_basis b₀ b j hj e f hf v
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨z, hz⟩ := (finiteHilbertEquiv b₀).surjective (W.symm v)
  have hv : v = W (finiteHilbertEquiv b₀ z) := by
    rw [hz, W.apply_symm_apply]
  rw [hv, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, W.symm_apply_apply,
    finiteHilbertOperator_apply, hMap, hMap, finiteHilbertOperator_apply]
  exact congrArg (finiteHilbertEquiv b₀) (map_dGamma f T S hTS z)

end
end SecondQuantization.Fermionic.AlgebraicFock

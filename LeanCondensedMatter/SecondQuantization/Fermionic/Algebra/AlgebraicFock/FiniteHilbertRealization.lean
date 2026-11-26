import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FiniteHilbertCreationAnnihilation

set_option linter.style.header false

/-!
# Finite-Hilbert realization of exterior-Fock operators

A finite ordered one-particle basis identifies exterior Fock space with the finite occupation
Hilbert space. The induced operator transport is an algebra equivalence. For an orthonormal
one-particle basis it also realizes smeared creation and annihilation as Hilbert adjoints.
Isometric changes between orthonormal one-particle bases are handled in `FiniteHilbertIsometry`.
-/

namespace SecondQuantization.Fermionic.AlgebraicFock

open scoped BigOperators

noncomputable section

variable {Mode V : Type*} [LinearOrder Mode] [Fintype Mode]
variable [AddCommGroup V] [Module ℂ V]

/-- Finite occupation-Hilbert coordinates on exterior Fock vectors, determined by a
one-particle basis. This is a linear equivalence, without an assertion of isometry. -/
def finiteHilbertEquiv (b : Module.Basis Mode ℂ V) :
    AlgebraicFock V ≃ₗ[ℂ] Common.FiniteHilbertFock (Occupation Mode) :=
  (occupationEquiv b).symm.trans Common.finiteHilbertFockEquiv

/-- Transport along a one-particle map carrying one indexed basis to another does
not change the occupation-Hilbert coordinates of an exterior vector. This
also applies to an algebraic one-particle space without an inner product. -/
theorem finiteHilbertEquiv_map_of_basis
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (b : Module.Basis Mode ℂ V) (c : Module.Basis Mode ℂ W)
    (j : V →ₗ[ℂ] W) (hj : ∀ i, j (b i) = c i) (x : AlgebraicFock V) :
    finiteHilbertEquiv c (ExteriorAlgebra.map j x) = finiteHilbertEquiv b x := by
  have h : (finiteHilbertEquiv c).toLinearMap.comp (ExteriorAlgebra.map j).toLinearMap =
      (finiteHilbertEquiv b).toLinearMap := by
    apply b.ExteriorAlgebra.ext
    intro n
    change finiteHilbertEquiv c (ExteriorAlgebra.map j (b.ExteriorAlgebra n)) =
      finiteHilbertEquiv b (b.ExteriorAlgebra n)
    have hn : ExteriorAlgebra.map j (b.ExteriorAlgebra n) = c.ExteriorAlgebra n := by
      rw [ExteriorAlgebra.basis_apply b n, ExteriorAlgebra.basis_apply c n,
        ExteriorAlgebra.map_apply_ιMulti]
      congr 1
      funext i
      exact hj _
    rw [hn]
    simp only [finiteHilbertEquiv, LinearEquiv.trans_apply, occupationEquiv_symm_exteriorBasis]
  exact DFunLike.congr_fun h x

/-- The operator realization in finite occupation-Hilbert coordinates determined by a
one-particle basis. No inner product on the one-particle space is needed for this transport. -/
def finiteHilbertOperatorAlgEquiv (b : Module.Basis Mode ℂ V) :
    (AlgebraicFock V →ₗ[ℂ] AlgebraicFock V) ≃ₐ[ℂ]
      (Common.FiniteHilbertFock (Occupation Mode) →L[ℂ]
        Common.FiniteHilbertFock (Occupation Mode)) :=
  ((finiteHilbertEquiv b).conjAlgEquiv ℂ).trans
    (Module.End.toContinuousLinearMap (Common.FiniteHilbertFock (Occupation Mode)))

/-- The finite-Hilbert operator realization acts on the corresponding vector coordinates. -/
theorem finiteHilbertOperator_apply (b : Module.Basis Mode ℂ V)
    (A : AlgebraicFock V →ₗ[ℂ] AlgebraicFock V) (Ψ : AlgebraicFock V) :
    finiteHilbertOperatorAlgEquiv b A (finiteHilbertEquiv b Ψ) =
      finiteHilbertEquiv b (A Ψ) := by
  change finiteHilbertEquiv b (A ((finiteHilbertEquiv b).symm (finiteHilbertEquiv b Ψ))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The one-particle sector of the bounded exterior-Fock realization carries
the original one-body operator. This transports the existing algebraic
one-particle identity without assuming an independent matrix model. -/
theorem finiteHilbertOperator_dGamma_oneParticle
    (b : Module.Basis Mode ℂ V) (T : V →ₗ[ℂ] V) (v : V) :
    finiteHilbertOperatorAlgEquiv b (dGamma V T)
        (finiteHilbertEquiv b (oneParticle V v)) =
      finiteHilbertEquiv b (oneParticle V (T v)) := by
  rw [finiteHilbertOperator_apply, dGamma_oneParticle]

/-- An orthonormal one-particle basis makes the finite-Hilbert realizations of smeared
creation and annihilation mutual adjoints. -/
theorem star_finiteHilbertOperator_create
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : OrthonormalBasis Mode ℂ H) (v : H) :
    star (finiteHilbertOperatorAlgEquiv b.toBasis (create H v)) =
      finiteHilbertOperatorAlgEquiv b.toBasis (annihilate H v) := by
  have hb (i : Mode) :
      star (finiteHilbertOperatorAlgEquiv b.toBasis (create H (b i))) =
        finiteHilbertOperatorAlgEquiv b.toBasis (annihilate H (b i)) := by
    have hdual : innerDual H (b i) = b.toBasis.coord i := by
      ext w
      change inner ℂ (b i) w = b.toBasis.repr w i
      rw [b.coe_toBasis_repr_apply, b.repr_apply_apply]
    have hann : annihilate H (b i) = annihilateDual H (b.toBasis.coord i) := by
      change annihilateDual H (innerDual H (b i)) = _
      rw [hdual]
    change star (Common.finiteHilbertOperatorAlgEquiv
      (occupationConjugate b.toBasis (create H (b i)))) =
      Common.finiteHilbertOperatorAlgEquiv (occupationConjugate b.toBasis (annihilate H (b i)))
    have hcreate := occupationConjugate_create b.toBasis i
    simp only [OrthonormalBasis.coe_toBasis] at hcreate
    rw [hcreate, hann, occupationConjugate_annihilateDual]
    exact SecondQuantization.Fermionic.star_finiteHilbertCreate i
  rw [← b.sum_repr v]
  simp only [map_sum, map_smul, (annihilate H).map_smulₛₗ, star_sum, star_smul,
    starRingEnd_apply, hb]

end
end SecondQuantization.Fermionic.AlgebraicFock

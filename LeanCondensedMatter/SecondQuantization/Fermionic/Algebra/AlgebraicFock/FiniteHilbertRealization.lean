import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FiniteHilbertCreationAnnihilation

set_option linter.style.header false

/-!
# Finite-Hilbert realization of exterior-Fock operators

A finite ordered one-particle basis identifies exterior Fock space with the finite occupation
Hilbert space. The induced operator transport is an algebra equivalence. For an orthonormal
one-particle basis it also realizes smeared creation and annihilation as Hilbert adjoints.
This does not yet identify the Hilbert norms obtained from different one-particle bases.
-/

namespace SecondQuantization.Fermionic.AlgebraicFock

open scoped BigOperators

noncomputable section

variable {Mode V : Type*} [LinearOrder Mode] [Fintype Mode]
variable [AddCommGroup V] [Module ℂ V]

/-- The operator realization in finite occupation-Hilbert coordinates determined by a
one-particle basis. No inner product on the one-particle space is needed for this transport. -/
def finiteHilbertOperatorAlgEquiv (b : Module.Basis Mode ℂ V) :
    (AlgebraicFock V →ₗ[ℂ] AlgebraicFock V) ≃ₐ[ℂ]
      (Common.FiniteHilbertFock (Occupation Mode) →L[ℂ]
        Common.FiniteHilbertFock (Occupation Mode)) :=
  (occupationConjugate b).trans Common.finiteHilbertOperatorAlgEquiv

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
    rw [occupationConjugate_create, hann, occupationConjugate_annihilateDual]
    exact SecondQuantization.Fermionic.star_finiteHilbertCreate i
  rw [← b.sum_repr v]
  simp only [map_sum, map_smul, (annihilate H).map_smulₛₗ, star_sum, star_smul, hb]

end
end SecondQuantization.Fermionic.AlgebraicFock

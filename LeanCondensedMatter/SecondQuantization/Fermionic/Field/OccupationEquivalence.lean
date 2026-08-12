import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FockSpace
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

set_option linter.style.header false

/-!
# Occupation and exterior-algebra Fock-space equivalence

A linearly ordered basis `b : Module.Basis Mode ℂ 𝓗₁` identifies the occupation-subset Fock space
with the algebraic exterior Fock space. The occupation basis state indexed by a finite subset is
sent to the corresponding ordered exterior-basis vector.

The equivalence is algebraic and requires neither finite-dimensionality nor a Hilbert-space
completion. `occupationConjugate` transports exterior-Fock endomorphisms into the occupation
representation through this equivalence.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Mode 𝓗₁ : Type*} [LinearOrder Mode]
variable [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The basis-induced linear equivalence from occupation-subset Fock space to the exterior-algebra
finite-particle Fock space.

The map sends the occupation basis state indexed by `n : Finset Mode` to the corresponding exterior
basis vector `b.ExteriorAlgebra n`. -/
noncomputable def occupationEquiv (b : Module.Basis Mode ℂ 𝓗₁) :
    OccupationFock Mode ≃ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  (b.ExteriorAlgebra).repr.symm

/-- Occupation basis vectors become the exterior-algebra basis vectors induced by `b`. -/
@[simp]
theorem occupationEquiv_basisState (b : Module.Basis Mode ℂ 𝓗₁) (n : Occupation Mode) :
    occupationEquiv b (basisState n) = b.ExteriorAlgebra n := by
  simpa [occupationEquiv, basisState, Common.basisState] using
    (b.ExteriorAlgebra.repr_symm_single_one n)

/-- Exterior-algebra basis vectors return to the corresponding occupation basis vectors. -/
theorem occupationEquiv_symm_exteriorBasis
    (b : Module.Basis Mode ℂ 𝓗₁) (n : Occupation Mode) :
    (occupationEquiv b).symm (b.ExteriorAlgebra n) = basisState n := by
  rw [← occupationEquiv_basisState]
  exact (occupationEquiv b).symm_apply_apply (basisState n)

/-- Taking exterior-basis coordinates after transporting an occupation state recovers that state. -/
@[simp]
theorem exteriorBasis_repr_occupationEquiv
    (b : Module.Basis Mode ℂ 𝓗₁) (Ψ : OccupationFock Mode) :
    (b.ExteriorAlgebra).repr (occupationEquiv b Ψ) = Ψ := by
  exact (b.ExteriorAlgebra).repr.apply_symm_apply Ψ

/-- The inverse transport is exactly the coordinate map in the induced exterior basis. -/
@[simp]
theorem occupationEquiv_symm_apply
    (b : Module.Basis Mode ℂ 𝓗₁) (Ψ : AlgebraicFock 𝓗₁) :
    (occupationEquiv b).symm Ψ = (b.ExteriorAlgebra).repr Ψ :=
  rfl

/-- Transport an exterior-Fock endomorphism into the occupation representation through a chosen
one-particle basis. -/
noncomputable def occupationConjugate
    (b : Module.Basis Mode ℂ 𝓗₁)
    (A : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  (occupationEquiv b).symm.toLinearMap.comp
    (A.comp (occupationEquiv b).toLinearMap)

@[simp]
theorem occupationEquiv_occupationConjugate_apply
    (b : Module.Basis Mode ℂ 𝓗₁)
    (A : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁)
    (Ψ : OccupationFock Mode) :
    occupationEquiv b (occupationConjugate b A Ψ) = A (occupationEquiv b Ψ) := by
  change
    occupationEquiv b
        ((occupationEquiv b).symm (A (occupationEquiv b Ψ))) =
      A (occupationEquiv b Ψ)
  exact (occupationEquiv b).apply_symm_apply _

end Field
end Fermionic
end SecondQuantization

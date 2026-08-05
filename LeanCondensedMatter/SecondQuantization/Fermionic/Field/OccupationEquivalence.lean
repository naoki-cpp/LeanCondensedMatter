import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FockSpace
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Mode
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

set_option linter.style.header false

/-!
# Occupation-basis equivalence for basis-independent fermionic Fock space

This module closes the representation-comparison part of F2 in issue #524. Once a linearly ordered
basis `b : Basis Mode ℂ 𝓗₁` is chosen for the one-particle space, mathlib supplies a basis
`b.ExteriorAlgebra` of the full exterior algebra indexed by finite subsets of `Mode`.

The existing occupation representation is exactly the free complex vector space on those finite
subsets:

```text
FockSpace Mode = Finset Mode →₀ ℂ.
```

Therefore the inverse coordinate map of `b.ExteriorAlgebra` gives a canonical linear equivalence
between the occupation-subset representation and the basis-independent exterior-algebra
representation. No finite-dimensionality assumption is required; only the chosen basis and its
linear order enter this comparison.
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
    FockSpace Mode ≃ₗ[ℂ] FiniteParticleFock 𝓗₁ :=
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
    (b : Module.Basis Mode ℂ 𝓗₁) (Ψ : FockSpace Mode) :
    (b.ExteriorAlgebra).repr (occupationEquiv b Ψ) = Ψ := by
  exact (b.ExteriorAlgebra).repr.apply_symm_apply Ψ

/-- The inverse transport is exactly the coordinate map in the induced exterior basis. -/
@[simp]
theorem occupationEquiv_symm_apply
    (b : Module.Basis Mode ℂ 𝓗₁) (Ψ : FiniteParticleFock 𝓗₁) :
    (occupationEquiv b).symm Ψ = (b.ExteriorAlgebra).repr Ψ :=
  rfl

end Field
end Fermionic
end SecondQuantization

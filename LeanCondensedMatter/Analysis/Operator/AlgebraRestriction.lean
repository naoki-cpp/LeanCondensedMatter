import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap

set_option linter.style.header false

/-!
# Restrict an endomorphism algebra to an invariant submodule

Mathlib supplies restriction of individual linear maps. This bundles restriction
as an algebra homomorphism when a subalgebra preserves the submodule.
-/

namespace Subalgebra

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The action of an endomorphism subalgebra on a submodule it preserves. -/
def restrictEnd (S : Subalgebra R (Module.End R V)) (p : Submodule R V)
    (hS : ∀ A ∈ S, ∀ x ∈ p, A x ∈ p) : S →ₐ[R] Module.End R p where
  toFun A := A.val.restrict (hS A.val A.property)
  map_one' := by apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  map_mul' A B := by apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  map_zero' := by apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  map_add' A B := by apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  commutes' c := by apply LinearMap.ext; intro x; apply Subtype.ext; rfl

end Subalgebra

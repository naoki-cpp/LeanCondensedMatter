import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Finite-component module endomorphisms

Scalar matrices act on the finite index of module-valued families. Their
action is linear in the matrix and commutes with a common componentwise
endomorphism. No topology or function-space structure is required.
-/

namespace FiniteComponents

noncomputable section

variable {K M ι : Type*}

section Semiring

variable [CommSemiring K] [AddCommMonoid M] [Module K M]

/-- Componentwise application, bundled as a linear map in the endomorphism. -/
def componentwiseLinear (ι : Type*) :
    (M →ₗ[K] M) →ₗ[K] ((ι → M) →ₗ[K] (ι → M)) where
  toFun A := A.compLeft ι
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

variable [Fintype ι]

/-- A finite internal matrix acting on the internal index and leaving the module-valued component intact. -/
noncomputable def internalOperator (S : Matrix ι ι K) : (ι → M) →ₗ[K] (ι → M) where
  toFun := fun ψ a => ∑ b : ι, S a b • ψ b
  map_add' := by
    intro ψ χ
    funext a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp]
theorem internalOperator_apply (S : Matrix ι ι K) (ψ : (ι → M)) (a : ι) :
    internalOperator S ψ a = ∑ b : ι, S a b • ψ b :=
  rfl

/-- The internal-matrix action is linear in the supplied internal matrix. -/
noncomputable def internalOperatorLinear :
    Matrix ι ι K →ₗ[K] ((ι → M) →ₗ[K] (ι → M)) where
  toFun := internalOperator
  map_add' := by
    intro S T
    apply LinearMap.ext
    intro ψ
    funext a
    simp [internalOperator, Finset.sum_add_distrib, add_smul]
  map_smul' := by
    intro c S
    apply LinearMap.ext
    intro ψ
    funext a
    simp [internalOperator, Finset.smul_sum, smul_smul]

end Semiring

section Ring

variable [CommRing K] [AddCommGroup M] [Module K M] [Fintype ι]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Componentwise endomorphisms Lie-commute with internal matrix operators. -/
theorem lie_compLeft_internalOperator_eq_zero
    (A : M →ₗ[K] M) (S : Matrix ι ι K) :
    ⁅A.compLeft ι, internalOperator S⁆ = 0 := by
  simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, sub_eq_zero]
  apply LinearMap.ext
  intro ψ
  funext a
  change A (∑ b : ι, S a b • ψ b) = ∑ b : ι, S a b • A (ψ b)
  rw [map_sum]
  simp


end Ring

end

end FiniteComponents

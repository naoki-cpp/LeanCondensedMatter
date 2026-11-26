import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Module.BigOperators
import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite-component Schwartz operator algebra

Componentwise spatial lifts and internal matrix operators on `ι → SchwartzMap ℝ ℂ`
are independent of the choice of internal index type and physical Hamiltonian.
The internal matrix action uses a finite index type.
-/

namespace SchwartzComponents1D

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

/-- Scalar complex Schwartz space used for each internal component. -/
abbrev Spatial := SchwartzKinetic1D.Space

/-- Complex Schwartz states indexed by internal components. -/
abbrev State (ι : Type*) := ι → Spatial

variable {ι : Type*}

/-- Lift a scalar Schwartz operator componentwise to an indexed state. -/
noncomputable def spatialLift (A : Spatial →ₗ[ℂ] Spatial) : State ι →ₗ[ℂ] State ι where
  toFun := fun ψ a => A (ψ a)
  map_add' := by
    intro ψ χ
    funext a
    simp
  map_smul' := by
    intro c ψ
    funext a
    simp

@[simp]
theorem spatialLift_apply (A : Spatial →ₗ[ℂ] Spatial) (ψ : State ι) (a : ι) :
    spatialLift A ψ a = A (ψ a) :=
  rfl

variable [Fintype ι]

/-- A finite internal matrix acting on the internal index and leaving the spatial wavefunction intact. -/
noncomputable def internalOperator (S : Matrix ι ι ℂ) : State ι →ₗ[ℂ] State ι where
  toFun := fun ψ a => ∑ b : ι, S a b • ψ b
  map_add' := by
    intro ψ χ
    funext a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp [smul_smul, mul_comm]

@[simp]
theorem internalOperator_apply (S : Matrix ι ι ℂ) (ψ : State ι) (a : ι) :
    internalOperator S ψ a = ∑ b : ι, S a b • ψ b :=
  rfl

/-- The internal-matrix action is complex-linear in the supplied internal matrix. -/
noncomputable def internalOperatorLinear :
    Matrix ι ι ℂ →ₗ[ℂ] (State ι →ₗ[ℂ] State ι) where
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
    simp [internalOperator, smul_smul]

/-- Componentwise spatial operators Lie-commute with internal matrix operators. -/
theorem lie_spatialLift_internalOperator_eq_zero
    (A : Spatial →ₗ[ℂ] Spatial) (S : Matrix ι ι ℂ) :
    ⁅spatialLift A, internalOperator S⁆ = 0 := by
  simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, sub_eq_zero]
  apply LinearMap.ext
  intro ψ
  funext a
  simp [internalOperator]

/-- Componentwise multiplication by a scalar Schwartz localizer. -/
noncomputable def multiplicationOperator (f : Spatial) : State ι →ₗ[ℂ] State ι :=
  spatialLift (SchwartzKinetic1D.multiplicationOperator f)

@[simp]
theorem multiplicationOperator_apply
    (f : Spatial) (ψ : State ι) (a : ι) (x : ℝ) :
    multiplicationOperator f ψ a x = f x * ψ a x :=
  rfl

/-- Multiplication localizers depend complex-linearly on the scalar Schwartz test function. -/
noncomputable def multiplicationLinear : Spatial →ₗ[ℂ] (State ι →ₗ[ℂ] State ι) where
  toFun := multiplicationOperator
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro ψ
    funext a
    ext x
    simp [multiplicationOperator]
    ring
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro ψ
    funext a
    ext x
    simp [multiplicationOperator]
    ring


end
end SchwartzComponents1D

import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-component Schwartz operator algebra

The state space `Fin 2 → SchwartzMap ℝ ℂ`, componentwise spatial lifts, internal matrix
operators, and their commutation identities are independent of any physical Hamiltonian.
The Schrödinger and velocity specializations live in
`QuantumMechanics.SingleParticle.Continuum.SchwartzTwoLevelSchrodinger1D`.
-/

namespace SchwartzTwoLevel1D

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

/-- Scalar complex Schwartz space used for each internal component. -/
abbrev Spatial := SchwartzKinetic1D.Space

/-- Two-component complex Schwartz two-level states. -/
abbrev State := Fin 2 → Spatial

/-- Complex `2 × 2` matrices acting on the two-level internal index. -/
abbrev InternalMatrix := InternalSpace.PauliMatrix

/-- Lift a scalar Schwartz operator componentwise to a two-component two-level state. -/
noncomputable def spatialLift (A : Spatial →ₗ[ℂ] Spatial) : State →ₗ[ℂ] State where
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
theorem spatialLift_apply (A : Spatial →ₗ[ℂ] Spatial) (ψ : State) (a : Fin 2) :
    spatialLift A ψ a = A (ψ a) :=
  rfl

/-- A finite internal matrix acting on the internal index and leaving the spatial wavefunction intact. -/
noncomputable def internalOperator (S : InternalMatrix) : State →ₗ[ℂ] State where
  toFun := fun ψ a => ∑ b : Fin 2, S a b • ψ b
  map_add' := by
    intro ψ χ
    funext a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp [smul_smul, mul_comm]

@[simp]
theorem internalOperator_apply (S : InternalMatrix) (ψ : State) (a : Fin 2) :
    internalOperator S ψ a = ∑ b : Fin 2, S a b • ψ b :=
  rfl

/-- The internal-matrix action is complex-linear in the supplied two-level matrix. -/
noncomputable def internalOperatorLinear :
    InternalMatrix →ₗ[ℂ] (State →ₗ[ℂ] State) where
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

@[simp]
theorem internalOperatorLinear_apply (S : InternalMatrix) :
    internalOperatorLinear S = internalOperator S :=
  rfl

/-- Spatial and internal operators commute because they act on independent factors. -/
theorem spatialLift_comp_internalOperator_comm
    (A : Spatial →ₗ[ℂ] Spatial) (S : InternalMatrix) :
    (spatialLift A).comp (internalOperator S) =
      (internalOperator S).comp (spatialLift A) := by
  apply LinearMap.ext
  intro ψ
  funext a
  simp [internalOperator]

/-- Componentwise spatial operators Lie-commute with internal matrix operators. -/
theorem lie_spatialLift_internalOperator_eq_zero
    (A : Spatial →ₗ[ℂ] Spatial) (S : InternalMatrix) :
    ⁅spatialLift A, internalOperator S⁆ = 0 := by
  simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]
  rw [spatialLift_comp_internalOperator_comm, sub_self]

/-- Two-level multiplication by a scalar Schwartz localizer. -/
noncomputable def multiplicationOperator (f : Spatial) : State →ₗ[ℂ] State :=
  spatialLift (SchwartzKinetic1D.multiplicationOperator f)

@[simp]
theorem multiplicationOperator_apply
    (f : Spatial) (ψ : State) (a : Fin 2) (x : ℝ) :
    multiplicationOperator f ψ a x = f x * ψ a x :=
  rfl

/-- Multiplication localizers depend complex-linearly on the scalar Schwartz test function. -/
noncomputable def multiplicationLinear : Spatial →ₗ[ℂ] (State →ₗ[ℂ] State) where
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

@[simp]
theorem multiplicationLinear_apply (f : Spatial) :
    multiplicationLinear f = multiplicationOperator f :=
  rfl


end
end SchwartzTwoLevel1D

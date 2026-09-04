import Mathlib.Tactic

set_option linter.style.header false

/-!
# Linear-map commutators

This module owns the ordinary commutator of complex-linear endomorphisms independently of any
particular quantum representation or second-quantization construction.

```text
[S,T] = S ∘ T - T ∘ S.
```

It also packages commutation with a fixed left operator as a linear endomorphism of the operator
space. Second-quantization and quantum layers may specialize this algebraic evolution without
redefining it.
-/

namespace ConservationLaw

/-- Ordinary commutator of two complex-linear endomorphisms. -/
noncomputable def linearCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  S.comp T - T.comp S

@[simp]
theorem linearCommutator_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) (v : V) :
    linearCommutator S T v = S (T v) - T (S v) :=
  rfl

/-- The ordinary commutator is linear in its right argument. -/
theorem linearCommutator_smul_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : ℂ) (S T : V →ₗ[ℂ] V) :
    linearCommutator S (q • T) = q • linearCommutator S T := by
  ext v
  simp [linearCommutator, smul_sub]

/-- Commutation with a fixed left operator, packaged as a linear map on endomorphisms. -/
noncomputable def commutatorEvolution {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun := fun T => linearCommutator S T
  map_add' := by
    intro A B
    ext v
    simp [linearCommutator]
    module
  map_smul' := by
    intro c A
    ext v
    simp [linearCommutator]
    module

@[simp]
theorem commutatorEvolution_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) :
    commutatorEvolution S T = linearCommutator S T :=
  rfl

/-- A scalar multiple of the identity commutes with every complex-linear endomorphism. -/
@[simp]
theorem linearCommutator_smul_id_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : V →ₗ[ℂ] V) (q : ℂ) :
    linearCommutator S (q • LinearMap.id) = 0 := by
  ext v
  simp [linearCommutator]

end ConservationLaw

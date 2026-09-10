import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Linear-map commutators

This module owns the ordinary commutator of complex-linear endomorphisms independently of any
particular quantum representation or second-quantization construction.

```text
[S,T] = S ∘ T - T ∘ S.
```

The raw fixed-sign bracket algebra is owned by `Analysis.Operator.ZetaCommutator`; this module keeps
the ordinary commutator as the semantic API used by conservation-law and current code. It also
packages commutation with a fixed left operator as a linear endomorphism of the operator space.
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

/-- The ordinary commutator is the `ζ = 1` specialization of the generic `ζ`-commutator. -/
theorem linearCommutator_eq_zetaCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) :
    linearCommutator S T = LinearMap.zetaCommutator 1 S T := by
  simp [linearCommutator, LinearMap.zetaCommutator]

/-- Leibniz rule for a commutator with a composition on the right:
`[M, A B] = [M,A] B + A [M,B]`. -/
theorem linearCommutator_comp_right
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M A B : V →ₗ[ℂ] V) :
    linearCommutator M (A.comp B) =
      (linearCommutator M A).comp B + A.comp (linearCommutator M B) := by
  simp only [linearCommutator_eq_zetaCommutator]
  simpa using (LinearMap.zetaCommutator_comp_right (1 : ℂ) 1 M A B)

/-- A commutator is additive over subtraction in its second argument. -/
theorem linearCommutator_sub_right
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (M A B : V →ₗ[ℂ] V) :
    linearCommutator M (A - B) =
      linearCommutator M A - linearCommutator M B := by
  apply LinearMap.ext
  intro v
  simp [linearCommutator]
  abel

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

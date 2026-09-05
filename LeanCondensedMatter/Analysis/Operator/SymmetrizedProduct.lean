import LeanCondensedMatter.Analysis.Operator.LinearCommutator
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Symmetrized products of linear operators

Pure algebra for the symmetric product

```text
1/2 {A,B} = 1/2 (AB + BA).
```

This module intentionally carries no localization, transport, conservation-law, quantum-mechanical,
or particle-statistics interpretation. Those meanings belong to downstream layers.
-/

namespace ConservationLaw

/-- Symmetrized composition `1/2 {A, B}` of two complex-linear endomorphisms. -/
noncomputable def symmetrizedProduct {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W) : W →ₗ[ℂ] W :=
  (1 / 2 : ℂ) • (A.comp B + B.comp A)

@[simp]
theorem symmetrizedProduct_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W) (v : W) :
    symmetrizedProduct A B v = (1 / 2 : ℂ) • (A (B v) + B (A v)) := by
  rfl

/-- The symmetrized product is symmetric in its two arguments. -/
theorem symmetrizedProduct_comm {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W) :
    symmetrizedProduct A B = symmetrizedProduct B A := by
  ext v
  simp [symmetrizedProduct, add_comm]

@[simp]
theorem symmetrizedProduct_zero_left {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) :
    symmetrizedProduct (0 : W →ₗ[ℂ] W) A = 0 := by
  ext v
  simp [symmetrizedProduct]

@[simp]
theorem symmetrizedProduct_zero_right {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) :
    symmetrizedProduct A (0 : W →ₗ[ℂ] W) = 0 := by
  rw [symmetrizedProduct_comm]
  exact symmetrizedProduct_zero_left A

/-- Scalar multiples of the identity behave as scalar quantities under symmetrization. -/
@[simp]
theorem symmetrizedProduct_smul_id {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : W →ₗ[ℂ] W) (q : ℂ) :
    symmetrizedProduct A (q • LinearMap.id) = q • A := by
  ext v
  simp [symmetrizedProduct]
  module

/-- If two operators commute, their symmetrized product reduces to ordinary composition. -/
theorem symmetrizedProduct_eq_comp_of_commutes {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B : W →ₗ[ℂ] W)
    (hAB : linearCommutator A B = 0) :
    symmetrizedProduct A B = A.comp B := by
  ext v
  have hzero : A (B v) - B (A v) = 0 := by
    have h := congrArg (fun T : W →ₗ[ℂ] W => T v) hAB
    simpa [linearCommutator] using h
  have hcomm : A (B v) = B (A v) := sub_eq_zero.mp hzero
  change (1 / 2 : ℂ) • (A (B v) + B (A v)) = A (B v)
  rw [← hcomm]
  module

/-- Reassociating two symmetrized products produces a double-commutator correction.

This identity is the representation-independent algebra behind the distinction between a generic
localized transport functional and a current density of the form `1/2 {v,m}`. -/
theorem symmetrizedProduct_nested {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A v m : W →ₗ[ℂ] W) :
    symmetrizedProduct (symmetrizedProduct A v) m =
      symmetrizedProduct A (symmetrizedProduct v m) +
        (1 / 4 : ℂ) • linearCommutator v (linearCommutator A m) := by
  ext x
  simp [symmetrizedProduct, linearCommutator]
  module

/-- If the outer localizer commutes with the transported quantity, nested symmetrization
reassociates without a correction. -/
theorem symmetrizedProduct_nested_eq_of_commutes
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A v m : W →ₗ[ℂ] W)
    (hAm : linearCommutator A m = 0) :
    symmetrizedProduct (symmetrizedProduct A v) m =
      symmetrizedProduct A (symmetrizedProduct v m) := by
  rw [symmetrizedProduct_nested A v m, hAm]
  simp [linearCommutator]

/-- The commutator acts as a derivation on the symmetrized product. -/
theorem linearCommutator_symmetrizedProduct {W : Type*} [AddCommGroup W] [Module ℂ W]
    (h A B : W →ₗ[ℂ] W) :
    linearCommutator h (symmetrizedProduct A B) =
      symmetrizedProduct (linearCommutator h A) B +
        symmetrizedProduct A (linearCommutator h B) := by
  ext v
  simp [linearCommutator, symmetrizedProduct]
  module

end ConservationLaw

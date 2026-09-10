import Mathlib.Tactic

set_option linter.style.header false

/-!
# ζ-commutators of linear endomorphisms

This module owns the representation-independent twisted commutator

```text
[A, B]_ζ = A ∘ B - ζ • (B ∘ A)
```

for complex-linear endomorphisms. The parameter `ζ` is a fixed scalar. In particular, this is not a
graded commutator: no degree or parity is attached to the individual operators.

Second-quantization code may specialize `ζ` to the bosonic or fermionic exchange sign, while
ordinary commutators and symmetric products arise at `ζ = 1` and `ζ = -1` respectively.
-/

namespace LinearMap

/-- The `ζ`-commutator `[A, B]_ζ = A ∘ B - ζ • (B ∘ A)`. -/
noncomputable def zetaCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A.comp B - ζ • (B.comp A)

@[simp]
theorem zetaCommutator_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B : V →ₗ[ℂ] V) (v : V) :
    zetaCommutator ζ A B v = A (B v) - ζ • B (A v) := by
  simp [zetaCommutator]

/-- The `ζ`-commutator is additive in its left argument. -/
theorem zetaCommutator_add_left {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator ζ (A + B) C = zetaCommutator ζ A C + zetaCommutator ζ B C := by
  ext v
  simp [zetaCommutator]
  module

/-- The `ζ`-commutator is additive in its right argument. -/
theorem zetaCommutator_add_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator ζ A (B + C) = zetaCommutator ζ A B + zetaCommutator ζ A C := by
  ext v
  simp [zetaCommutator]
  module

/-- Scalar multiples factor out of both arguments of the `ζ`-commutator. -/
theorem zetaCommutator_smul_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ c d : ℂ) (A B : V →ₗ[ℂ] V) :
    zetaCommutator ζ (c • A) (d • B) = (c * d) • zetaCommutator ζ A B := by
  simp only [zetaCommutator, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, smul_sub]
  congr 2 <;> ring

/-- Reorder a product from a supplied `ζ`-commutator value. -/
theorem comp_eq_add_smul_comp_of_zetaCommutator_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) {A B C : V →ₗ[ℂ] V}
    (h : zetaCommutator ζ A B = C) :
    A.comp B = C + ζ • (B.comp A) := by
  have h' : A.comp B - ζ • (B.comp A) = C := by
    simpa [zetaCommutator] using h
  exact (sub_eq_iff_eq_add).mp h'

/-- Reversing the arguments multiplies an involutive `ζ`-commutator by `-ζ`. -/
theorem zetaCommutator_swap_of_sq_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (hζ : ζ * ζ = 1) (A B : V →ₗ[ℂ] V) :
    zetaCommutator ζ B A = (-ζ) • zetaCommutator ζ A B := by
  have hneg : (-ζ) * ζ = -1 := by
    calc
      (-ζ) * ζ = -(ζ * ζ) := by ring
      _ = -1 := by rw [hζ]
  simp only [zetaCommutator, smul_sub, smul_smul]
  rw [hneg, neg_one_smul]
  module

/-- The self `ζ`-commutator is `(1 - ζ) A²`. -/
theorem zetaCommutator_self {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A : V →ₗ[ℂ] V) :
    zetaCommutator ζ A A = (1 - ζ) • A.comp A := by
  simp [zetaCommutator, sub_smul]

/-- Product rule when the composition occurs in the right argument.

The exchange factor on the left is the product `ζ * η`; this is the valid fixed-sign identity and
must not be replaced by a naive same-`ζ` Leibniz rule. -/
theorem zetaCommutator_comp_right
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ η : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator (ζ * η) A (B.comp C) =
      (zetaCommutator ζ A B).comp C +
        ζ • B.comp (zetaCommutator η A C) := by
  ext v
  simp [zetaCommutator, smul_sub, smul_smul]

/-- Product rule when the composition occurs in the left argument. -/
theorem zetaCommutator_comp_left
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ η : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator (ζ * η) (A.comp B) C =
      A.comp (zetaCommutator η B C) +
        η • (zetaCommutator ζ A C).comp B := by
  ext v
  simp [zetaCommutator, smul_sub, smul_smul]

end LinearMap

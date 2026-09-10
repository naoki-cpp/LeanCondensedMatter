import Mathlib.Tactic

set_option linter.style.header false

/-!
# ζ-commutators of linear endomorphisms

The fixed-sign bracket is `[A,B]_ζ = A ∘ B - ζ • (B ∘ A)`. It is not a graded commutator: `ζ` is
a scalar, not a sign inferred from operator degrees. Products therefore use mixed signs `ζ * η`.
-/

namespace LinearMap

/-- The fixed-sign bracket `[A,B]_ζ = A ∘ B - ζ • (B ∘ A)`. -/
noncomputable def zetaCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A.comp B - ζ • (B.comp A)

@[simp]
theorem zetaCommutator_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B : V →ₗ[ℂ] V) (v : V) :
    zetaCommutator ζ A B v = A (B v) - ζ • B (A v) := by
  simp [zetaCommutator]

/-- Additivity in the left argument. -/
theorem zetaCommutator_add_left {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator ζ (A + B) C = zetaCommutator ζ A C + zetaCommutator ζ B C := by
  ext v
  simp [zetaCommutator]
  module

/-- Additivity in the right argument. -/
theorem zetaCommutator_add_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator ζ A (B + C) = zetaCommutator ζ A B + zetaCommutator ζ A C := by
  ext v
  simp [zetaCommutator]
  module

/-- Scalar multiples factor out of both arguments. -/
theorem zetaCommutator_smul_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ c d : ℂ) (A B : V →ₗ[ℂ] V) :
    zetaCommutator ζ (c • A) (d • B) = (c * d) • zetaCommutator ζ A B := by
  simp only [zetaCommutator, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, smul_sub]
  congr 2 <;> ring

/-- Reorder a product from a supplied bracket value. -/
theorem comp_eq_add_smul_comp_of_zetaCommutator_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ζ : ℂ) {A B C : V →ₗ[ℂ] V}
    (h : zetaCommutator ζ A B = C) : A.comp B = C + ζ • (B.comp A) := by
  have h' : A.comp B - ζ • (B.comp A) = C := by
    simpa [zetaCommutator] using h
  exact (sub_eq_iff_eq_add).mp h'

/-- Reversal for an involutive sign. -/
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

/-- The self bracket is `(1 - ζ) A²`. -/
theorem zetaCommutator_self {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ : ℂ) (A : V →ₗ[ℂ] V) :
    zetaCommutator ζ A A = (1 - ζ) • A.comp A := by
  simp [zetaCommutator, sub_smul]

/-- Mixed-sign product rule in the right argument. -/
theorem zetaCommutator_comp_right
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ η : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator (ζ * η) A (B.comp C) =
      (zetaCommutator ζ A B).comp C + ζ • B.comp (zetaCommutator η A C) := by
  ext v
  simp [zetaCommutator, smul_sub, smul_smul]

/-- Mixed-sign product rule in the left argument. -/
theorem zetaCommutator_comp_left
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ζ η : ℂ) (A B C : V →ₗ[ℂ] V) :
    zetaCommutator (ζ * η) (A.comp B) C =
      A.comp (zetaCommutator η B C) + η • (zetaCommutator ζ A C).comp B := by
  ext v
  simp only [zetaCommutator_apply, coe_comp, Function.comp_apply, add_apply,
    map_sub, map_smul, smul_apply]
  rw [mul_comm ζ η]
  module

end LinearMap

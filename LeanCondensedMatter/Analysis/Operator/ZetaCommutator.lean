import Mathlib.Tactic

set_option linter.style.header false

/-!
# ζ-commutators of linear endomorphisms

The fixed-sign bracket is `[A,B]_ζ = A ∘ B - ζ • (B ∘ A)`. It is not a graded commutator: `ζ` is
a scalar, not a sign inferred from operator degrees. Products therefore use mixed signs `ζ * η`.
This module also owns the finite exchange-peel identity obtained by repeatedly applying a supplied
scalar exchange relation through an ordered product of endomorphisms.
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

/-- The exchange terms generated while pushing one labelled endomorphism through a finite tail. -/
noncomputable def operatorPeelSum {Label M : Type*} [AddCommMonoid M] [Module ℂ M]
    (operator : Label → M →ₗ[ℂ] M) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) : List Label → M →ₗ[ℂ] M
  | [] => 0
  | D :: t =>
      exchangeCoeff C D • (t.map operator).prod +
        ζ • ((operator D).comp (operatorPeelSum operator exchangeCoeff ζ C t))

@[simp]
theorem operatorPeelSum_nil {Label M : Type*} [AddCommMonoid M] [Module ℂ M]
    (operator : Label → M →ₗ[ℂ] M) (exchangeCoeff : Label → Label → ℂ)
    (ζ : ℂ) (C : Label) :
    operatorPeelSum operator exchangeCoeff ζ C [] = 0 := rfl

/-- Repeatedly apply a scalar exchange relation while pushing one endomorphism through a finite
ordered product. -/
theorem operator_comp_prod_eq_operatorPeelSum
    {Label M : Type*} [AddCommMonoid M] [Module ℂ M]
    (operator : Label → M →ₗ[ℂ] M) (exchangeCoeff : Label → Label → ℂ) (ζ : ℂ)
    (hExchange : ∀ C D,
      (operator C).comp (operator D) =
        exchangeCoeff C D • (LinearMap.id : M →ₗ[ℂ] M) +
          ζ • ((operator D).comp (operator C)))
    (C : Label) (l : List Label) :
    (operator C).comp ((l.map operator).prod) =
      operatorPeelSum operator exchangeCoeff ζ C l +
        ζ ^ l.length • ((l.map operator).prod.comp (operator C)) := by
  induction l with
  | nil =>
      simp [operatorPeelSum, Module.End.one_eq_id]
  | cons D t ih =>
      apply LinearMap.ext
      intro x
      have hexchange := DFunLike.congr_fun (hExchange C D) ((t.map operator).prod x)
      have hih := DFunLike.congr_fun ih x
      simp only [List.map_cons, List.prod_cons, Module.End.mul_eq_comp, operatorPeelSum,
        List.length_cons, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hexchange hih ⊢
      rw [hexchange, hih]
      simp only [map_add, map_smul, pow_succ]
      module

end LinearMap

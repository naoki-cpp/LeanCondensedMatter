import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Symmetrized products in associative algebras

The bilinear product `(1 / 2) • (a * b + b * a)` is defined on arbitrary
associative ring algebras over a field. Operator evaluation and identity lemmas
express its endomorphism representation.
-/

namespace LinearMap

variable {K : Type*} [Field K]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The symmetric product as a bilinear map on an algebra. -/
noncomputable def symmetrizedProductBilinear
    (A : Type*) [Ring A] [Algebra K A] :
    A →ₗ[K] A →ₗ[K] A :=
  (1 / 2 : K) • (LinearMap.mul K A + (LinearMap.mul K A).flip)

/-- Symmetric multiplication obtained by evaluating the bilinear map. -/
noncomputable def symmetrizedProduct {A : Type*} [Ring A] [Algebra K A]
    (a b : A) : A :=
  symmetrizedProductBilinear (K := K) A a b

theorem symmetrizedProductBilinear_apply
    {A : Type*} [Ring A] [Algebra K A] (a b : A) :
    symmetrizedProductBilinear (K := K) A a b = symmetrizedProduct (K := K) a b :=
  rfl

theorem symmetrizedProduct_eq {A : Type*} [Ring A] [Algebra K A] (a b : A) :
    symmetrizedProduct (K := K) a b = (1 / 2 : K) • (a * b + b * a) :=
  rfl

@[simp]
theorem symmetrizedProduct_apply {W : Type*} [AddCommGroup W] [Module K W]
    (A B : W →ₗ[K] W) (v : W) :
    symmetrizedProduct (K := K) A B v = (1 / 2 : K) • (A (B v) + B (A v)) :=
  rfl

section Algebra

variable {A : Type*} [Ring A] [Algebra K A]

/-- Symmetric multiplication is commutative. -/
theorem symmetrizedProduct_comm (a b : A) :
    symmetrizedProduct (K := K) a b = symmetrizedProduct (K := K) b a := by
  simp only [symmetrizedProduct_eq, add_comm]

@[simp]
theorem symmetrizedProduct_zero_left (a : A) :
    symmetrizedProduct (K := K) 0 a = 0 := by
  simp [symmetrizedProduct_eq]

@[simp]
theorem symmetrizedProduct_zero_right (a : A) :
    symmetrizedProduct (K := K) a 0 = 0 := by
  simp [symmetrizedProduct_eq]

/-- Reassociating symmetric multiplication produces a double commutator. -/
theorem symmetrizedProduct_nested (a v m : A) :
    symmetrizedProduct (K := K) (symmetrizedProduct (K := K) a v) m =
      symmetrizedProduct (K := K) a (symmetrizedProduct (K := K) v m) +
        (1 / 4 : K) • ⁅v, ⁅a, m⁆⁆ := by
  have hquarter : (1 / 4 : K) = (1 / 2 : K) * (1 / 2 : K) := by
    rw [show (4 : K) = (2 : K) ^ 2 by ring]
    simp only [one_div, pow_two, mul_inv_rev]
  rw [hquarter]
  simp only [symmetrizedProduct_eq, LieRing.of_associative_ring_bracket, mul_add,
    add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_smul, mul_assoc]
  module

/-- If the outer factors commute, symmetric multiplication reassociates. -/
theorem symmetrizedProduct_nested_eq_of_commutes (a v m : A) (ham : ⁅a, m⁆ = 0) :
    symmetrizedProduct (K := K) (symmetrizedProduct (K := K) a v) m =
      symmetrizedProduct (K := K) a (symmetrizedProduct (K := K) v m) := by
  rw [symmetrizedProduct_nested, ham]
  simp

/-- The commutator is a derivation of the symmetric product. -/
theorem lie_symmetrizedProduct (h a b : A) :
    ⁅h, symmetrizedProduct (K := K) a b⁆ =
      symmetrizedProduct (K := K) ⁅h, a⁆ b +
        symmetrizedProduct (K := K) a ⁅h, b⁆ := by
  simp only [symmetrizedProduct_eq, LieRing.of_associative_ring_bracket, mul_add,
    add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, mul_assoc]
  module

end Algebra

section Half

variable [NeZero (2 : K)]

/-- Scalar multiples of the identity behave as scalar quantities under symmetrization. -/
@[simp]
theorem symmetrizedProduct_smul_id {W : Type*} [AddCommGroup W] [Module K W]
    (A : W →ₗ[K] W) (q : K) :
    symmetrizedProduct (K := K) A (q • LinearMap.id) = q • A := by
  ext v
  simp only [symmetrizedProduct_apply, one_div, smul_apply, id_coe, id_eq, map_smul,
    smul_add]
  rw [← two_smul K, smul_smul]
  have h2 : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ (NeZero.ne (2 : K))
  simp only [h2, one_smul]

/-- If two operators commute, their symmetrized product reduces to ordinary composition. -/
theorem symmetrizedProduct_eq_comp_of_commutes {W : Type*} [AddCommGroup W] [Module K W]
    (A B : W →ₗ[K] W)
    (hAB : ⁅A, B⁆ = 0) :
    symmetrizedProduct (K := K) A B = A.comp B := by
  ext v
  have hzero : A (B v) - B (A v) = 0 := by
    have h := congrArg (fun T : W →ₗ[K] W => T v) hAB
    simpa [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp] using h
  have hcomm : A (B v) = B (A v) := sub_eq_zero.mp hzero
  rw [symmetrizedProduct_apply]
  rw [← hcomm]
  change (1 / 2 : K) • (A (B v) + A (B v)) = A (B v)
  rw [← two_smul K (A (B v)), smul_smul]
  have h2 : (1 / 2 : K) * 2 = 1 := by
    simpa only [one_div] using (inv_mul_cancel₀ (NeZero.ne (2 : K)))
  rw [h2, one_smul]

end Half

end LinearMap

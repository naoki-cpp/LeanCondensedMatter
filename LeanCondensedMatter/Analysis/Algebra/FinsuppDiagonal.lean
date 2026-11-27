import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# Diagonal endomorphisms of free modules

The pointwise function algebra acts coordinatewise on finitely supported
vectors. The index type need not be finite.
-/

namespace Finsupp

variable {R Config : Type*} [CommSemiring R]

private noncomputable def diagonalOperatorLinear (a : Config → R) :
    (Config →₀ R) →ₗ[R] (Config →₀ R) where
  toFun x := Finsupp.onFinset x.support (fun i => a i * x i)
    (fun i hi => Finsupp.mem_support_iff.mpr (fun h => hi (by rw [h, mul_zero])))
  map_add' x y := by
    ext i
    change a i * (x i + y i) = a i * x i + a i * y i
    exact mul_add _ _ _
  map_smul' c x := by
    ext i
    change a i * (c * x i) = c * (a i * x i)
    exact mul_left_comm _ _ _

/-- Pointwise scalar multiplication defines an algebra representation on a free module. -/
noncomputable def diagonalOperator :
    (Config → R) →ₐ[R] ((Config →₀ R) →ₗ[R] (Config →₀ R)) where
  toFun := diagonalOperatorLinear
  map_zero' := by
    ext x i
    change (0 : R) * x i = 0
    exact zero_mul _
  map_one' := by
    ext x i
    change (1 : R) * x i = x i
    exact one_mul _
  map_add' a b := by
    ext x i
    change (a i + b i) * x i = a i * x i + b i * x i
    exact add_mul _ _ _
  map_mul' a b := by
    ext x i
    change (a i * b i) * x i = a i * (b i * x i)
    exact mul_assoc _ _ _
  commutes' k := by
    ext x i
    rfl

/-- Diagonal endomorphisms multiply each coordinate by its specified scalar. -/
theorem diagonalOperator_apply (a : Config → R) (x : Config →₀ R) (c : Config) :
    diagonalOperator a x c = a c * x c :=
  rfl

@[simp]
theorem diagonalOperator_single (a : Config → R) (c : Config) :
    diagonalOperator a (Finsupp.single c 1) = a c • Finsupp.single c 1 := by
  classical
  ext i
  rw [diagonalOperator_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : c = i
  · subst i
    rfl
  · rw [Finsupp.single_eq_of_ne h, mul_zero, mul_zero]

/-- Pointwise multiplication is represented by composition. -/
theorem diagonalOperator_comp (a b : Config → R) :
    (diagonalOperator a).comp (diagonalOperator b) = diagonalOperator (fun c => a c * b c) := by
  have h := map_mul (diagonalOperator (Config := Config)) a b
  rw [Module.End.mul_eq_comp] at h
  exact h.symm

/-- The representation recovers the scalar family from its action on basis vectors. -/
theorem diagonalOperator_injective :
    Function.Injective (diagonalOperator (R := R) (Config := Config)) := by
  intro a b h
  funext c
  have hc := congrArg (fun A : (Config →₀ R) →ₗ[R] (Config →₀ R) =>
    A (Finsupp.single c 1) c) h
  simpa [diagonalOperator_apply] using hc

end Finsupp

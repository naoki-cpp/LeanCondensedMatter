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
    (Config →₀ R) →ₗ[R] (Config →₀ R) :=
  Finsupp.basisSingleOne.constr R (fun c => a c • Finsupp.single c 1)

private theorem diagonalOperatorLinear_single (a : Config → R) (c : Config) :
    diagonalOperatorLinear a (Finsupp.single c 1) = a c • Finsupp.single c 1 := by
  simpa only [Finsupp.coe_basisSingleOne] using
    (Finsupp.basisSingleOne.constr_basis R (fun i : Config => a i • Finsupp.single i 1) c)

/-- Pointwise scalar multiplication defines an algebra representation on a free module. -/
noncomputable def diagonalOperator :
    (Config → R) →ₐ[R] ((Config →₀ R) →ₗ[R] (Config →₀ R)) where
  toFun := diagonalOperatorLinear
  map_zero' := by
    apply Finsupp.basisSingleOne.ext
    intro c
    simp [Finsupp.coe_basisSingleOne, diagonalOperatorLinear_single]
  map_one' := by
    apply Finsupp.basisSingleOne.ext
    intro c
    simp [Finsupp.coe_basisSingleOne, diagonalOperatorLinear_single]
  map_add' := by
    intro a b
    apply Finsupp.basisSingleOne.ext
    intro c
    simp [Finsupp.coe_basisSingleOne, diagonalOperatorLinear_single, add_smul]
  map_mul' := by
    intro a b
    rw [Module.End.mul_eq_comp]
    apply Finsupp.basisSingleOne.ext
    intro c
    simp [Finsupp.coe_basisSingleOne, diagonalOperatorLinear_single, smul_smul, mul_comm]
  commutes' := by
    intro k
    apply Finsupp.basisSingleOne.ext
    intro c
    simp [Finsupp.coe_basisSingleOne, diagonalOperatorLinear_single]

@[simp]
theorem diagonalOperator_single (a : Config → R) (c : Config) :
    diagonalOperator a (Finsupp.single c 1) = a c • Finsupp.single c 1 :=
  diagonalOperatorLinear_single a c

/-- Diagonal endomorphisms multiply each coordinate by its specified scalar. -/
theorem diagonalOperator_apply (a : Config → R) (x : Config →₀ R) (c : Config) :
    diagonalOperator a x c = a c * x c := by
  let eval : (Config →₀ R) →ₗ[R] R := Finsupp.lapply c
  have hmap : eval.comp (diagonalOperator a) = a c • eval := by
    apply Finsupp.basisSingleOne.ext
    intro i
    simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, diagonalOperator_single,
      map_smul, LinearMap.smul_apply]
    by_cases h : i = c
    · subst i
      simp [eval]
    · simp [eval, h]
  have hx := congrArg (fun L => L x) hmap
  simpa only [eval, LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
    smul_eq_mul] using hx

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

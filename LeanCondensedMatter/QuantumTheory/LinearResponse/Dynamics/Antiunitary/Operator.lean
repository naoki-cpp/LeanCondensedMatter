import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Conjugation of bounded operators by an antiunitary

An antiunitary map on a finite-dimensional Hilbert space acts on bounded
complex-linear operators by A ↦ Θ A Θ⁻¹. The induced operator action is
conjugate-linear, multiplicative, and preserves the adjoint. It does not
assume Θ² = 1 on the Hilbert space.
-/

namespace QuantumTheory.LinearResponse

noncomputable section

namespace AntiunitaryMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (Θ : AntiunitaryMap H)

/-- The inverse of a bijective antiunitary map on Hilbert-space vectors. -/
noncomputable def inverse (x : H) : H :=
  Function.surjInv Θ.bijective.2 x

@[simp]
theorem apply_inverse (x : H) : Θ.toFun (Θ.inverse x) = x :=
  Function.rightInverse_surjInv Θ.bijective.2 x

@[simp]
theorem inverse_apply (x : H) : Θ.inverse (Θ.toFun x) = x := by
  apply Θ.bijective.1
  simp

theorem inverse_add (x y : H) :
    Θ.inverse (x + y) = Θ.inverse x + Θ.inverse y := by
  apply Θ.bijective.1
  rw [Θ.map_add, Θ.apply_inverse, Θ.apply_inverse, Θ.apply_inverse]

theorem inverse_smul (c : ℂ) (x : H) :
    Θ.inverse (c • x) = ((starRingEnd ℂ) c) • Θ.inverse x := by
  apply Θ.bijective.1
  rw [Θ.map_smul, Θ.apply_inverse, Θ.apply_inverse]
  simp

theorem map_neg (x : H) : Θ.toFun (-x) = -(Θ.toFun x) := by
  simpa only [neg_one_smul, map_neg] using Θ.map_smul (-1 : ℂ) x

theorem map_zero : Θ.toFun (0 : H) = 0 := by
  have h := Θ.map_smul (0 : ℂ) (0 : H)
  simpa only [zero_smul] using h

/-- Antiunitary conjugation sends a bounded complex-linear operator to
another bounded complex-linear operator. Finite dimensionality supplies
continuity of the resulting linear map. -/
noncomputable def conjugateOperator [FiniteDimensional ℂ H]
    (A : H →L[ℂ] H) : H →L[ℂ] H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Θ.toFun (A (Θ.inverse x))
      map_add' := by
        intro x y
        rw [Θ.inverse_add, map_add, Θ.map_add]
      map_smul' := by
        intro c x
        rw [Θ.inverse_smul, map_smul, Θ.map_smul]
        simp }

@[simp]
theorem conjugateOperator_apply [FiniteDimensional ℂ H]
    (A : H →L[ℂ] H) (x : H) :
    Θ.conjugateOperator A x = Θ.toFun (A (Θ.inverse x)) := rfl

@[simp]
theorem conjugateOperator_add [FiniteDimensional ℂ H]
    (A B : H →L[ℂ] H) :
    Θ.conjugateOperator (A + B) =
      Θ.conjugateOperator A + Θ.conjugateOperator B := by
  ext x
  simp only [conjugateOperator_apply, ContinuousLinearMap.add_apply, map_add, Θ.map_add]

@[simp]
theorem conjugateOperator_mul [FiniteDimensional ℂ H]
    (A B : H →L[ℂ] H) :
    Θ.conjugateOperator (A * B) =
      Θ.conjugateOperator A * Θ.conjugateOperator B := by
  ext x
  simp only [conjugateOperator_apply, ContinuousLinearMap.mul_apply_eq_comp]
  rw [Θ.inverse_apply]

@[simp]
theorem conjugateOperator_smul [FiniteDimensional ℂ H]
    (c : ℂ) (A : H →L[ℂ] H) :
    Θ.conjugateOperator (c • A) =
      ((starRingEnd ℂ) c) • Θ.conjugateOperator A := by
  ext x
  simp only [conjugateOperator_apply, ContinuousLinearMap.smul_apply, smul_apply]
  exact Θ.map_smul c (A (Θ.inverse x))

@[simp]
theorem conjugateOperator_one [FiniteDimensional ℂ H] :
    Θ.conjugateOperator (1 : H →L[ℂ] H) = 1 := by
  ext x
  simp only [conjugateOperator_apply, one_apply, Θ.apply_inverse]

@[simp]
theorem conjugateOperator_zero [FiniteDimensional ℂ H] :
    Θ.conjugateOperator (0 : H →L[ℂ] H) = 0 := by
  ext x
  simp only [conjugateOperator_apply, zero_apply, Θ.map_zero]

/-- The induced operator action preserves adjoints. No vector-level
involution hypothesis is required. -/
theorem conjugateOperator_star [FiniteDimensional ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) :
    Θ.conjugateOperator (star A) = star (Θ.conjugateOperator A) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  calc
    inner ℂ (Θ.conjugateOperator (star A) x) y =
        inner ℂ (Θ.toFun ((star A) (Θ.inverse x)))
          (Θ.toFun (Θ.inverse y)) := by
      rw [Θ.apply_inverse]
      rfl
    _ = (starRingEnd ℂ) (inner ℂ ((star A) (Θ.inverse x)) (Θ.inverse y)) :=
      Θ.inner_map _ _
    _ = (starRingEnd ℂ) (inner ℂ (Θ.inverse x) (A (Θ.inverse y))) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (Θ.toFun (Θ.inverse x)) (Θ.toFun (A (Θ.inverse y))) :=
      (Θ.inner_map _ _).symm
    _ = inner ℂ x (Θ.conjugateOperator A y) := by
      rw [Θ.apply_inverse]
      rfl

/-- For a spin-half antiunitary with square minus identity, the induced
action on bounded observables is involutive. -/
theorem conjugateOperator_involutive_of_square_neg [FiniteDimensional ℂ H]
    (hsq : ∀ x : H, Θ.toFun (Θ.toFun x) = -x)
    (A : H →L[ℂ] H) :
    Θ.conjugateOperator (Θ.conjugateOperator A) = A := by
  have hinv : ∀ x : H, Θ.inverse x = -(Θ.toFun x) := by
    intro x
    apply Θ.bijective.1
    rw [Θ.apply_inverse, Θ.map_neg, hsq]
    simp
  ext x
  simp only [conjugateOperator_apply, hinv]
  rw [Θ.map_neg, Θ.map_neg, hsq]
  simp

end AntiunitaryMap

end
end QuantumTheory.LinearResponse

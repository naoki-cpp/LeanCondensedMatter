import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.RCLike.Basic

set_option linter.style.header false

/-!
# Operator conjugation by an antiunitary equivalence

The induced action on bounded operators is A ↦ Θ A Θ⁻¹. Both Θ and Θ⁻¹
are continuous conjugate-linear equivalences, so their composition around
a complex-linear bounded operator is automatically bounded and linear.
Finite dimensionality is needed only below to prove continuity of the
induced action on the *space of operators* for the exponential theorem.

No assumption Θ² = 1 is used for operator conjugation or exponential covariance.
-/

namespace QuantumTheory.LinearResponse

noncomputable section

namespace AntiunitaryMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (Θ : AntiunitaryMap H)

/-- Conjugation of a bounded operator by a state-space antiunitary.
Unlike the earlier linear-map construction, boundedness does not require
the Hilbert space to be finite dimensional. -/
noncomputable def conjugateOperator (A : H →L[ℂ] H) : H →L[ℂ] H where
  toFun := fun x => Θ.equiv (A (Θ.equiv.symm x))
  map_add' := by
    intro x y
    simp only [map_add]
  map_smul' := by
    intro c x
    calc
      Θ.equiv (A (Θ.equiv.symm (c • x))) =
          Θ.equiv (A (((starRingEnd ℂ) c) • Θ.equiv.symm x)) := by
        rw [Θ.equiv.symm.map_smulₛₗ]
      _ = Θ.equiv (((starRingEnd ℂ) c) • A (Θ.equiv.symm x)) := by
        rw [A.map_smul]
      _ = ((starRingEnd ℂ) ((starRingEnd ℂ) c)) •
          Θ.equiv (A (Θ.equiv.symm x)) := by
        rw [Θ.equiv.map_smulₛₗ]
      _ = (RingHom.id ℂ) c • Θ.equiv (A (Θ.equiv.symm x)) := by simp
  cont := Θ.equiv.continuous.comp (A.continuous.comp Θ.equiv.symm.continuous)

@[simp]
theorem conjugateOperator_apply (A : H →L[ℂ] H) (x : H) :
    Θ.conjugateOperator A x = Θ.equiv (A (Θ.equiv.symm x)) := rfl

@[simp]
theorem conjugateOperator_add (A B : H →L[ℂ] H) :
    Θ.conjugateOperator (A + B) =
      Θ.conjugateOperator A + Θ.conjugateOperator B := by
  ext x
  simp only [conjugateOperator_apply, add_apply, map_add]

@[simp]
theorem conjugateOperator_mul (A B : H →L[ℂ] H) :
    Θ.conjugateOperator (A * B) =
      Θ.conjugateOperator A * Θ.conjugateOperator B := by
  ext x
  change Θ.equiv (A (B (Θ.equiv.symm x))) =
    Θ.equiv (A (Θ.equiv.symm (Θ.equiv (B (Θ.equiv.symm x)))))
  rw [Θ.equiv.symm_apply_apply]

@[simp]
theorem conjugateOperator_smul (c : ℂ) (A : H →L[ℂ] H) :
    Θ.conjugateOperator (c • A) =
      ((starRingEnd ℂ) c) • Θ.conjugateOperator A := by
  ext x
  simp only [conjugateOperator_apply, smul_apply]
  exact Θ.equiv.map_smulₛₗ c (A (Θ.equiv.symm x))

@[simp]
theorem conjugateOperator_one :
    Θ.conjugateOperator (1 : H →L[ℂ] H) = 1 := by
  ext x
  change Θ.equiv (Θ.equiv.symm x) = x
  exact Θ.equiv.apply_symm_apply x

@[simp]
theorem conjugateOperator_zero :
    Θ.conjugateOperator (0 : H →L[ℂ] H) = 0 := by
  ext x
  change Θ.equiv (0 : H) = 0
  exact map_zero Θ.equiv

/-- The conjugation action is a unital ring homomorphism on bounded
endomorphisms, even for infinite-dimensional state spaces. -/
noncomputable def conjugateOperatorRingHom :
    (H →L[ℂ] H) →+* (H →L[ℂ] H) where
  toFun := Θ.conjugateOperator
  map_one' := Θ.conjugateOperator_one
  map_mul' := Θ.conjugateOperator_mul
  map_zero' := Θ.conjugateOperator_zero
  map_add' := Θ.conjugateOperator_add

/-- The ring action is real-linear; its continuity in finite dimensions
gives a direct route to exponential covariance. -/
private noncomputable def conjugateOperatorRealLinear :
    (H →L[ℂ] H) →ₗ[ℝ] (H →L[ℂ] H) where
  toFun := Θ.conjugateOperator
  map_add' := Θ.conjugateOperator_add
  map_smul' := by
    intro r A
    change Θ.conjugateOperator ((r : ℂ) • A) =
      (r : ℂ) • Θ.conjugateOperator A
    rw [Θ.conjugateOperator_smul]
    have hr : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) :=
      RCLike.conj_ofReal (K := ℂ) r
    rw [hr]

/-- Antiunitary conjugation commutes with bounded-operator exponentiation.
Finite-dimensionality is used to establish continuity on the operator space. -/
theorem conjugateOperator_exp [FiniteDimensional ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) :
    Θ.conjugateOperator (NormedSpace.exp A) =
      NormedSpace.exp (Θ.conjugateOperator A) := by
  haveI : FiniteDimensional ℂ (H →L[ℂ] H) := inferInstance
  haveI : FiniteDimensional ℝ (H →L[ℂ] H) :=
    FiniteDimensional.complexToReal _
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hcont : Continuous (Θ.conjugateOperator : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
    Θ.conjugateOperatorRealLinear.continuous_of_finiteDimensional
  exact NormedSpace.map_exp (Θ.conjugateOperatorRingHom) hcont A

end AntiunitaryMap

end
end QuantumTheory.LinearResponse

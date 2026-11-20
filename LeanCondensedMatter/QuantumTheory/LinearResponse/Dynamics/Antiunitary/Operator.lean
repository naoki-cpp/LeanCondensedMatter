import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
    simp only [Θ.equiv.symm.map_smulₛₗ, A.map_smul, Θ.equiv.map_smulₛₗ]
    simp
  cont := Θ.equiv.continuous.comp (A.continuous.comp Θ.equiv.symm.continuous)

@[simp]
theorem conjugateOperator_apply (A : H →L[ℂ] H) (x : H) :
    Θ.conjugateOperator A x = Θ.equiv (A (Θ.equiv.symm x)) := rfl

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
  let f : (H →L[ℂ] H) →+* (H →L[ℂ] H) :=
    { toFun := Θ.conjugateOperator
      map_one' := by ext x; exact Θ.equiv.apply_symm_apply x
      map_mul' := Θ.conjugateOperator_mul
      map_zero' := by ext x; exact map_zero Θ.equiv
      map_add' := by
        intro B C
        ext x
        simp only [conjugateOperator_apply, add_apply, map_add] }
  have hcont : Continuous (Θ.conjugateOperator : (H →L[ℂ] H) → (H →L[ℂ] H)) := by
    let f : (H →L[ℂ] H) →ₗ[ℝ] (H →L[ℂ] H) :=
      { f.toAddMonoidHom with
        map_smul' := by
          intro r B
          change Θ.conjugateOperator ((r : ℂ) • B) =
            (r : ℂ) • Θ.conjugateOperator B
          rw [Θ.conjugateOperator_smul]
          have hr : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) :=
            RCLike.conj_ofReal (K := ℂ) r
          rw [hr] }
    exact f.continuous_of_finiteDimensional
  exact NormedSpace.map_exp f hcont A

end AntiunitaryMap

end
end QuantumTheory.LinearResponse

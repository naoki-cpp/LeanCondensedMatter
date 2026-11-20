import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

set_option linter.style.header false

/-!
# Operator conjugation by an antiunitary equivalence

The induced action on bounded operators is A ↦ Θ A Θ⁻¹. Both Θ and Θ⁻¹
are continuous conjugate-linear equivalences, so their composition around
a complex-linear bounded operator is automatically bounded and linear.
The induced action on the *space of operators* is continuous by Mathlib's
semilinear arrow congruence, without requiring finite dimensionality.

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
noncomputable def conjugateOperator (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (Θ.equiv.arrowCongrSL Θ.equiv) A

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
      ((starRingEnd ℂ) c) • Θ.conjugateOperator A :=
  (Θ.equiv.arrowCongrSL Θ.equiv).map_smulₛₗ c A

/-- Antiunitary conjugation commutes with bounded-operator exponentiation
on any complete complex inner-product space. -/
theorem conjugateOperator_exp [CompleteSpace H]
    (A : H →L[ℂ] H) :
    Θ.conjugateOperator (NormedSpace.exp A) =
      NormedSpace.exp (Θ.conjugateOperator A) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let f : (H →L[ℂ] H) →+* (H →L[ℂ] H) :=
    { toFun := Θ.conjugateOperator
      map_one' := by ext x; exact Θ.equiv.apply_symm_apply x
      map_mul' := Θ.conjugateOperator_mul
      map_zero' := (Θ.equiv.arrowCongrSL Θ.equiv).map_zero
      map_add' := (Θ.equiv.arrowCongrSL Θ.equiv).map_add }
  have hcont : Continuous (Θ.conjugateOperator : (H →L[ℂ] H) → (H →L[ℂ] H)) := by
    exact (Θ.equiv.arrowCongrSL Θ.equiv).continuous
  exact NormedSpace.map_exp f hcont A

end AntiunitaryMap

end
end QuantumTheory.LinearResponse

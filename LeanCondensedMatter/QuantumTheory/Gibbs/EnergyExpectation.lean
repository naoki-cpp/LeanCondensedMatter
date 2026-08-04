import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Energy expectation values

A bounded observable has a self-adjoint complex expectation in every density state. The physical
real energy expectation is obtained losslessly through `Complex.selfAdjointEquiv`, rather than by
projecting an arbitrary complex scalar to its real part.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The spectral series used by the energy expectation is summable. -/
theorem summable_energyExpValue_term (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
        (Hop.1 (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)) :=
  ρ.summable_expectation_term Hop.1

/-- The self-adjoint complex scalar representing the expectation of a bounded observable. -/
noncomputable def energyExpectationSelfAdjoint
    (ρ : DensityOperator H) (Hop : Observable H) : selfAdjoint ℂ :=
  ⟨ρ.expectation Hop.1,
    ρ.expectation_isSelfAdjoint_of_isSymmetric Hop.2.isSymmetric⟩

/-- The real expectation value of a bounded observable in a density state. -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  Complex.selfAdjointEquiv (energyExpectationSelfAdjoint ρ Hop)

/-- The canonical complex expectation is exactly the complex embedding of the real energy value. -/
@[simp]
theorem DensityOperator.expectation_observable (ρ : DensityOperator H) (Hop : Observable H) :
    ρ.expectation Hop.1 = (energyExpValue ρ Hop : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [energyExpValue, energyExpectationSelfAdjoint, Complex.selfAdjointEquiv] using
      ρ.expectation_im_eq_zero_of_isSymmetric Hop.2.isSymmetric

end QuantumTheory

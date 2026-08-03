import LeanCondensedMatter.QuantumTheory.DensityOperator.Purity
import LeanCondensedMatter.QuantumTheory.FiniteDimensional.Expectation

/-!
# Finite-dimensional purity formula

For the canonical density-state type, spectral purity agrees in finite dimensions with the ordinary
matrix trace of `ρ²`.
-/

noncomputable section

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- In finite dimensions, purity is the real part of the ordinary matrix trace `Tr(ρ²)`. -/
theorem DensityOperator.purity_eq_linearMap_trace_sq (ρ : DensityOperator H) :
    purity ρ =
      (LinearMap.trace ℂ H
        ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H)).re := by
  calc
    purity ρ = (ρ.expectation ρ.op).re := ρ.expectation_op_re.symm
    _ = (LinearMap.trace ℂ H
        ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H)).re :=
      congrArg Complex.re (ρ.expectation_eq_linearMap_trace ρ.op)

end QuantumTheory

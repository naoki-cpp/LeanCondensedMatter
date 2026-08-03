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

/-- In finite dimensions, the ordinary matrix trace `Tr(ρ²)` is the complex embedding of purity. -/
theorem DensityOperator.linearMap_trace_sq_eq_purity (ρ : DensityOperator H) :
    LinearMap.trace ℂ H
      ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = (purity ρ : ℂ) := by
  calc
    LinearMap.trace ℂ H
        ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = ρ.expectation ρ.op :=
      (ρ.expectation_eq_linearMap_trace ρ.op).symm
    _ = (purity ρ : ℂ) := ρ.expectation_op

end QuantumTheory

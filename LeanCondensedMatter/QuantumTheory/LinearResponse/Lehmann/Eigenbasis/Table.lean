import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.FiniteTable
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Data

set_option linter.style.header false

/-! # Scalar evaluation tables from eigenbasis operator data -/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forget an operator-level eigenbasis response problem to the scalar data needed for finite
Lehmann evaluation. -/
noncomputable def finiteLehmannTableOfEigenbasis
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) : FiniteLehmannTable ι where
  energy := data.energy
  probability := data.probability
  matrixA := fun m n => inner ℂ (data.basis m) (A (data.basis n))
  matrixB := fun m n => inner ℂ (data.basis m) (B (data.basis n))

/-- The scalar adapter preserves the canonical ordered transition exactly. -/
@[simp]
theorem finiteLehmannTableTransitionData_ofEigenbasis
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) :
    finiteLehmannTableTransitionData system.hbar
        (finiteLehmannTableOfEigenbasis system data A B) mn =
      eigenbasisTransitionData system data A B mn := rfl

/-- For a finite spectral index, scalar-table evaluation is exactly the theorem-level eigenbasis
Lehmann series.  This is the main operator-to-calculation bridge. -/
theorem finiteLehmannTableResponse_ofEigenbasis
    [Fintype ι]
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    finiteLehmannTableResponse system.hbar omega eta
        (finiteLehmannTableOfEigenbasis system data A B) =
      eigenbasisLehmannSeries system data A B omega eta := by
  rw [eigenbasisLehmannSeries_eq_finite_sum]
  simp [finiteLehmannTableResponse, LehmannTransitionData.frequencyTerm]

end
end LinearResponse
end QuantumTheory

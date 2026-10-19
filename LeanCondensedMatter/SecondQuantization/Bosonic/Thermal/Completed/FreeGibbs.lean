import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannSummability
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Heat
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator

set_option linter.style.header false

/-!
# Completed free-boson heat and Gibbs operators

For arbitrary bosonic mode types, nonnegative one-particle energies define a bounded completed
free heat operator. Summability of the occupation Boltzmann weights makes this operator trace
class and gives the canonical pure-point Gibbs density operator and trace normalization.
The finite-mode positive-energy theorem supplies this summability hypothesis when applicable.
No bounded bosonic ladder operator is introduced.
-/

namespace SecondQuantization
namespace Bosonic

open QuantumTheory
open ContinuousLinearMap

noncomputable section

variable {Mode : Type*}

/-- The bounded completed free-boson heat operator `exp (-β H₀)`. -/
noncomputable def completedFreeHeatOperator
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i) :
    CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode :=
  Common.completedDiagonalHeatOperator (freeEigenvalue ε) β 0 hβ
    (freeEigenvalue_nonneg ε hε)

@[simp]
theorem completedFreeHeatOperator_basisState
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (n : Occupation Mode) :
    completedFreeHeatOperator ε β hβ hε (completedBasisState n) =
      (Real.exp (-β * freeEigenvalue ε n) : ℂ) • completedBasisState n := by
  simpa [completedFreeHeatOperator, completedBasisState] using
    (Common.completedDiagonalHeatOperator_basisState
      (freeEigenvalue ε) β 0 hβ (freeEigenvalue_nonneg ε hε) n)

/-- The completed free heat operator has norm at most one for nonnegative one-particle energies. -/
theorem norm_completedFreeHeatOperator_le_one
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i) :
    ‖completedFreeHeatOperator ε β hβ hε‖ ≤ 1 := by
  simpa [completedFreeHeatOperator] using
    (Common.norm_completedDiagonalHeatOperator_le
      (freeEigenvalue ε) β 0 hβ (freeEigenvalue_nonneg ε hε))

/-- Summable occupation Boltzmann weights make the completed free heat operator trace class,
without requiring finitely many modes. -/
theorem completedFreeHeatOperator_isTraceClass
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    IsTraceClass (completedFreeHeatOperator ε β hβ hε) := by
  apply (isTraceClass_iff_eigenbasisGibbsSummable_of_basis_action
    (completedFreeHeatOperator ε β hβ hε)
    completedOccupationHilbertBasis (freeEigenvalue ε) β ?_).2
  · exact hsum
  · intro n
    rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
    rfl

/-- The trace of completed free heat data equals the algebraic bosonic partition function. -/
theorem completedFreeHeatOperator_trace_eq_freeGibbsPartition
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    (completedFreeHeatOperator_isTraceClass ε β hβ hε hsum).trace =
      freeGibbsPartition ε β := by
  rw [freeGibbsPartition_eq_coe_eigenbasisPartitionFunction ε β]
  exact heatTrace_eq_eigenbasisPartitionFunction_of_basis_action
    (completedFreeHeatOperator ε β hβ hε)
    (completedFreeHeatOperator_isTraceClass ε β hβ hε hsum)
    completedOccupationHilbertBasis (freeEigenvalue ε) β
    (fun n => by
      rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
      rfl)

/-- Canonical completed free-boson Gibbs density operator under occupation Gibbs summability. -/
noncomputable def completedFreeGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    DensityOperator (CompletedFockSpace Mode) :=
  eigenbasisGibbsDensityOperator completedOccupationHilbertBasis
    (freeEigenvalue ε) β hsum

@[simp]
theorem completedFreeGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β)
    (n : Occupation Mode) :
    (completedFreeGibbsDensityOperator ε β hsum).op (completedBasisState n) =
      (eigenbasisGibbsProbability (freeEigenvalue ε) β n : ℂ) •
        completedBasisState n := by
  simpa [completedFreeGibbsDensityOperator, completedOccupationHilbertBasis,
    completedBasisState] using
    eigenbasisGibbsDensityOperator_apply_basis
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β hsum n

/-- Normalize the completed free heat operator to obtain its canonical Gibbs density operator. -/
theorem inv_freeGibbsPartition_smul_completedFreeHeatOperator_eq_completedFreeGibbsDensityOperator_op
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    (freeGibbsPartition ε β)⁻¹ •
        completedFreeHeatOperator ε β hβ hε =
      (completedFreeGibbsDensityOperator ε β hsum).op := by
  rw [freeGibbsPartition_eq_coe_eigenbasisPartitionFunction ε β]
  simpa [completedFreeGibbsDensityOperator] using
    (inv_partition_smul_heat_eq_eigenbasisGibbsDensityOperator_op
      (completedFreeHeatOperator ε β hβ hε)
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β hsum
      (fun n => by
        rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
        rfl))

end
end Bosonic
end SecondQuantization

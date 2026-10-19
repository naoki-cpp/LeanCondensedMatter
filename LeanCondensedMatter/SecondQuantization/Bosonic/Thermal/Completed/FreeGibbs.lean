import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannSummability
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Heat
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator

set_option linter.style.header false

/-!
# Completed free-boson heat and Gibbs operators

For arbitrary bosonic mode types, nonnegative one-particle energies already define a bounded
completed free heat operator because every occupation configuration has finite support. For finitely
many modes with strictly positive energies, the free Boltzmann weights are summable; this upgrades
the heat operator to trace class and connects it to the generic pure-point Gibbs construction.

The resulting bounded heat operator is trace class, its trace is the existing convergence-aware
bosonic partition function, and normalization gives the canonical completed Gibbs density operator.
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

/-- The free heat operator is trace class on an arbitrary mode type whenever the
occupation Boltzmann weights are summable. -/
theorem completedFreeHeatOperator_isTraceClass_of_summable
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

/-- The completed free-boson Gibbs state on any mode type with summable occupation weights. -/
noncomputable def completedFreeGibbsDensityOperatorOfSummable
    (ε : Mode → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    DensityOperator (CompletedFockSpace Mode) :=
  eigenbasisGibbsDensityOperator completedOccupationHilbertBasis
    (freeEigenvalue ε) β hsum

@[simp]
theorem completedFreeGibbsDensityOperatorOfSummable_apply_basis
    (ε : Mode → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β)
    (n : Occupation Mode) :
    (completedFreeGibbsDensityOperatorOfSummable ε β hsum).op (completedBasisState n) =
      (eigenbasisGibbsProbability (freeEigenvalue ε) β n : ℂ) •
        completedBasisState n := by
  simpa [completedFreeGibbsDensityOperatorOfSummable, completedOccupationHilbertBasis,
    completedBasisState] using
    eigenbasisGibbsDensityOperator_apply_basis
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β hsum n

/-- Normalization of the arbitrary-mode free heat operator agrees with the canonical Gibbs
density operator whenever the occupation partition sum converges. -/
theorem inv_freeGibbsPartition_smul_completedFreeHeatOperator_eq_completedFreeGibbsDensityOperatorOfSummable_op
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    (freeGibbsPartition ε β)⁻¹ •
        completedFreeHeatOperator ε β hβ hε =
      (completedFreeGibbsDensityOperatorOfSummable ε β hsum).op := by
  rw [freeGibbsPartition_eq_coe_eigenbasisPartitionFunction ε β]
  simpa [completedFreeGibbsDensityOperatorOfSummable] using
    (inv_partition_smul_heat_eq_eigenbasisGibbsDensityOperator_op
      (completedFreeHeatOperator ε β hβ hε)
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β hsum
      (fun n => by
        rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
        rfl))

variable [Finite Mode]

/-- The completed free heat operator is trace class under positive mode energies. -/
theorem completedFreeHeatOperator_isTraceClass
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    IsTraceClass
      (completedFreeHeatOperator ε β hβ (fun i => (hε i).le)) :=
  completedFreeHeatOperator_isTraceClass_of_summable ε β hβ
    (fun i => (hε i).le) (eigenbasisGibbsSummable_freeEigenvalue ε β hβ hε)

/-- The trace of the completed free heat operator is the existing free bosonic partition
function. -/
theorem completedFreeHeatOperator_trace_eq_freeGibbsPartition
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    (completedFreeHeatOperator_isTraceClass ε β hβ hε).trace =
      freeGibbsPartition ε β := by
  rw [freeGibbsPartition_eq_coe_eigenbasisPartitionFunction ε β]
  exact heatTrace_eq_eigenbasisPartitionFunction_of_basis_action
    (completedFreeHeatOperator ε β hβ (fun i => (hε i).le))
    (completedFreeHeatOperator_isTraceClass ε β hβ hε)
    completedOccupationHilbertBasis (freeEigenvalue ε) β
    (fun n => by
      rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
      rfl)

/-- The canonical completed free-boson Gibbs density operator. -/
noncomputable def completedFreeGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    DensityOperator (CompletedFockSpace Mode) :=
  completedFreeGibbsDensityOperatorOfSummable ε β
    (eigenbasisGibbsSummable_freeEigenvalue ε β hβ hε)

@[simp]
theorem completedFreeGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i)
    (n : Occupation Mode) :
    (completedFreeGibbsDensityOperator ε β hβ hε).op (completedBasisState n) =
      (eigenbasisGibbsProbability (freeEigenvalue ε) β n : ℂ) •
        completedBasisState n := by
  simpa [completedFreeGibbsDensityOperator, completedFreeGibbsDensityOperatorOfSummable,
    completedOccupationHilbertBasis,
    completedBasisState] using
    eigenbasisGibbsDensityOperator_apply_basis
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β
      (eigenbasisGibbsSummable_freeEigenvalue ε β hβ hε) n

/-- Normalizing the completed free heat operator by the bosonic partition function gives the
canonical completed Gibbs density operator. -/
theorem inv_freeGibbsPartition_smul_completedFreeHeatOperator_eq_completedFreeGibbsDensityOperator_op
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    (freeGibbsPartition ε β)⁻¹ •
        completedFreeHeatOperator ε β hβ (fun i => (hε i).le) =
      (completedFreeGibbsDensityOperator ε β hβ hε).op := by
  rw [freeGibbsPartition_eq_coe_eigenbasisPartitionFunction ε β]
  simpa [completedFreeGibbsDensityOperator, completedFreeGibbsDensityOperatorOfSummable] using
    (inv_partition_smul_heat_eq_eigenbasisGibbsDensityOperator_op
      (completedFreeHeatOperator ε β hβ (fun i => (hε i).le))
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β
      (eigenbasisGibbsSummable_freeEigenvalue ε β hβ hε)
      (fun n => by
        rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
        rfl))

end
end Bosonic
end SecondQuantization

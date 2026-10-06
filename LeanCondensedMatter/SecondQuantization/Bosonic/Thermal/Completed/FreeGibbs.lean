import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Heat
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator

set_option linter.style.header false

/-!
# Completed free-boson heat and Gibbs operators

For finitely many bosonic modes with positive one-particle energies, the occupation basis remains
infinite but the free Boltzmann weights are summable. This module combines that existing bosonic
summability theorem with the statistics-independent completed diagonal heat operator and the generic
pure-point Gibbs construction.

The resulting bounded heat operator is trace class, its trace is the existing convergence-aware
bosonic partition function, and normalization gives the canonical completed Gibbs density operator.
No bounded bosonic ladder operator is introduced.
-/

namespace SecondQuantization
namespace Bosonic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Nonnegative one-particle energies give a nonnegative many-boson free energy. -/
theorem freeEigenvalue_nonneg (ε : Mode → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (n : Occupation Mode) :
    0 ≤ freeEigenvalue ε n := by
  rw [freeEigenvalue_eq_sum_univ]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hε i)

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

/-- Positive one-particle energies make the free occupation Boltzmann weights absolutely summable. -/
theorem purePointGibbsSummable_freeEigenvalue
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    PurePointGibbsSummable (freeEigenvalue ε) β := by
  unfold PurePointGibbsSummable
  have hsum := summable_boltzmannWeight ε β (fun i => mul_pos hβ (hε i))
  simpa [purePointBoltzmannWeight, boltzmannWeight, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)] using hsum

/-- The convergence-aware algebraic bosonic partition function is the canonical pure-point
partition function of the completed occupation representation. -/
theorem freeGibbsPartition_eq_coe_purePointPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    freeGibbsPartition ε β =
      (purePointPartitionFunction (freeEigenvalue ε) β : ℂ) := by
  rw [freeGibbsPartition_eq_tsum ε β (fun i => mul_pos hβ (hε i))]
  congr 1
  apply tsum_congr
  intro n
  rfl

/-- The completed free heat operator is trace class under positive mode energies. -/
theorem completedFreeHeatOperator_isTraceClass
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    IsTraceClass
      (completedFreeHeatOperator ε β hβ (fun i => (hε i).le)) := by
  apply (isTraceClass_iff_purePointGibbsSummable_of_basis_action
    (completedFreeHeatOperator ε β hβ (fun i => (hε i).le))
    completedOccupationHilbertBasis (freeEigenvalue ε) β ?_).2
  · exact purePointGibbsSummable_freeEigenvalue ε β hβ hε
  · intro n
    rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
    rfl

/-- The trace of the completed free heat operator is the existing free bosonic partition
function. -/
theorem completedFreeHeatOperator_trace_eq_freeGibbsPartition
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    (completedFreeHeatOperator_isTraceClass ε β hβ hε).trace =
      freeGibbsPartition ε β := by
  have htrace := heatTrace_eq_purePointPartitionFunction_of_basis_action
    (completedFreeHeatOperator ε β hβ (fun i => (hε i).le))
    (completedFreeHeatOperator_isTraceClass ε β hβ hε)
    completedOccupationHilbertBasis (freeEigenvalue ε) β
    (fun n => by
      rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
      rfl)
  rw [freeGibbsPartition_eq_coe_purePointPartitionFunction ε β hβ hε]
  exact htrace

/-- The canonical completed free-boson Gibbs density operator. -/
noncomputable def completedFreeGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    DensityOperator (CompletedFockSpace Mode) :=
  purePointGibbsDensityOperator completedOccupationHilbertBasis
    (freeEigenvalue ε) β (purePointGibbsSummable_freeEigenvalue ε β hβ hε)

@[simp]
theorem completedFreeGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i)
    (n : Occupation Mode) :
    (completedFreeGibbsDensityOperator ε β hβ hε).op (completedBasisState n) =
      (purePointGibbsProbability (freeEigenvalue ε) β n : ℂ) •
        completedBasisState n := by
  simpa [completedFreeGibbsDensityOperator, completedOccupationHilbertBasis,
    completedBasisState] using
    purePointGibbsDensityOperator_apply_basis
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β
      (purePointGibbsSummable_freeEigenvalue ε β hβ hε) n

/-- Normalizing the completed free heat operator by the bosonic partition function gives the
canonical completed Gibbs density operator. -/
theorem inv_freeGibbsPartition_smul_completedFreeHeatOperator_eq_completedFreeGibbsDensityOperator_op
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    (freeGibbsPartition ε β)⁻¹ •
        completedFreeHeatOperator ε β hβ (fun i => (hε i).le) =
      (completedFreeGibbsDensityOperator ε β hβ hε).op := by
  rw [freeGibbsPartition_eq_coe_purePointPartitionFunction ε β hβ hε]
  simpa [completedFreeGibbsDensityOperator] using
    (inv_partition_smul_heat_eq_purePointGibbsDensityOperator_op
      (completedFreeHeatOperator ε β hβ (fun i => (hε i).le))
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β
      (purePointGibbsSummable_freeEigenvalue ε β hβ hε)
      (fun n => by
        rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
        rfl))

end
end Bosonic
end SecondQuantization

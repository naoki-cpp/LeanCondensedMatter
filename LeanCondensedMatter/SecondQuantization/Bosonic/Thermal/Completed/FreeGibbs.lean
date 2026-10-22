import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannSummability
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Heat
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator

set_option linter.style.header false

/-!
# Completed free-boson heat and Gibbs operators

For arbitrary bosonic mode types, nonnegative one-particle energies define the bounded
physical heat operator exp(-βH). When its occupation weights are summable, its trace
and normalized operator coincide with the explicit-μ grand-canonical construction
in Common.Thermal at μ = 0. The grand-canonical density for arbitrary μ is owned
directly by Common.grandCanonicalGibbsDensityOperator: there is no silent μ = 0
bosonic density constructor or second normalization implementation here.
No bounded bosonic ladder operator is introduced.
-/

namespace SecondQuantization
namespace Bosonic

open QuantumTheory
open ContinuousLinearMap

noncomputable section

variable {Mode : Type*}

/-- At zero chemical potential, the grand-canonical excitation generator
reduces to the physical free-boson energy. -/
private theorem grandCanonicalEnergy_zero_eq_freeEigenvalue (ε : Mode → ℝ) :
    Common.grandCanonicalEnergy (Config := Occupation Mode) ε 0 = freeEigenvalue ε := by
  funext n
  simp [Common.grandCanonicalEnergy, freeEigenvalue]

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

/-- The trace of the physical free heat operator is the explicit grand-canonical
partition function specialized to zero chemical potential. -/
theorem completedFreeHeatOperator_trace_eq_grandCanonicalPartitionFunction_zero
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    (completedFreeHeatOperator_isTraceClass ε β hβ hε hsum).trace =
      (Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β 0 : ℂ) := by
  rw [Common.grandCanonicalPartitionFunction,
    grandCanonicalEnergy_zero_eq_freeEigenvalue]
  exact heatTrace_eq_eigenbasisPartitionFunction_of_basis_action
    (completedFreeHeatOperator ε β hβ hε)
    (completedFreeHeatOperator_isTraceClass ε β hβ hε hsum)
    completedOccupationHilbertBasis (freeEigenvalue ε) β
    (fun n => by
      rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
      rfl)

/-- At μ = 0 the physical Boltzmann heat operator normalizes to the shared
grand-canonical Gibbs density. For arbitrary μ the thermal generator is H - μ N,
not the physical heat operator exp(-βH) appearing here. -/
theorem inv_grandCanonicalPartitionFunction_zero_smul_completedFreeHeatOperator_eq_gibbs
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 ≤ ε i)
    (hsum : EigenbasisGibbsSummable (freeEigenvalue ε) β) :
    ((Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β 0)⁻¹ : ℂ) •
        completedFreeHeatOperator ε β hβ hε =
      (Common.grandCanonicalGibbsDensityOperator
        (Config := Occupation Mode) ε β 0
        (by
          rw [grandCanonicalEnergy_zero_eq_freeEigenvalue]
          exact hsum)).op := by
  simpa [Common.grandCanonicalPartitionFunction, Common.grandCanonicalGibbsDensityOperator,
    grandCanonicalEnergy_zero_eq_freeEigenvalue, completedOccupationHilbertBasis] using
    (inv_partition_smul_heat_eq_eigenbasisGibbsDensityOperator_op
      (completedFreeHeatOperator ε β hβ hε)
      (completedOccupationHilbertBasis (Mode := Mode))
      (freeEigenvalue ε) β hsum
      (fun n => by
        rw [completedOccupationHilbertBasis_apply, completedFreeHeatOperator_basisState]
        rfl))

/-- Normalize the bosonic heat operator generated by `K = H - μ N̂`
to obtain the shared grand-canonical state at chemical potential `μ`.

This is an actual application of the grand-canonical reference-shift
invariance: replace the spectrum by `ε - μ`, reuse the already proved
zero-chemical-potential heat normalization, then shift the reference
back simultaneously in the spectrum and chemical potential. -/
theorem inv_grandCanonicalPartitionFunction_smul_completedFreeHeatOperator_eq_gibbs
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 < β)
    (hgap : ∀ i, 0 ≤ ε i - μ)
    (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) :
    ((Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β μ)⁻¹ : ℂ) •
        completedFreeHeatOperator (fun i => ε i - μ) β hβ hgap =
      (Common.grandCanonicalGibbsDensityOperator
        (Config := Occupation Mode) ε β μ hsum).op := by
  have hshifted : EigenbasisGibbsSummable
      (freeEigenvalue (fun i => ε i - μ)) β :=
    (Common.grandCanonicalGibbsSummable_iff_shifted
      (Config := Occupation Mode) ε β μ).1 hsum
  have hzero : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode)
        (fun i => ε i - μ) 0) β := by
    rw [grandCanonicalEnergy_zero_eq_freeEigenvalue]
    exact hshifted
  have hpartition :
      Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β μ =
        Common.grandCanonicalPartitionFunction (Config := Occupation Mode)
          (fun i => ε i - μ) β 0 := by
    simpa only [sub_add_cancel, zero_add] using
      (Common.grandCanonicalPartitionFunction_shift_invariant
        (Config := Occupation Mode) (fun i => ε i - μ) β 0 μ)
  have hdensity :
      Common.grandCanonicalGibbsDensityOperator
          (Config := Occupation Mode) ε β μ hsum =
        Common.grandCanonicalGibbsDensityOperator
          (Config := Occupation Mode) (fun i => ε i - μ) β 0 hzero := by
    simpa only [sub_add_cancel, zero_add] using
      (Common.grandCanonicalGibbsDensityOperator_shift_invariant
        (Config := Occupation Mode) (fun i => ε i - μ) β 0 μ hzero)
  rw [hpartition, hdensity]
  exact inv_grandCanonicalPartitionFunction_zero_smul_completedFreeHeatOperator_eq_gibbs
    (fun i => ε i - μ) β hβ hgap hshifted

/-- The grand-canonical algebraic trace equals the actual trace of the
completed free heat operator for the grand-canonical generator
`K = H - μ N̂`. This identifies the formerly separate occupation-trace
and completed trace-class normalizations at arbitrary explicit μ. -/
theorem grandCanonicalAlgebraicPartition_eq_completedFreeHeatOperator_trace
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 < β)
    (hgap : ∀ i, 0 ≤ ε i - μ)
    (hsum : EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β) :
    grandCanonicalAlgebraicPartition ε β μ =
      (completedFreeHeatOperator_isTraceClass (fun i => ε i - μ) β hβ hgap
        ((Common.grandCanonicalGibbsSummable_iff_shifted
          (Config := Occupation Mode) ε β μ).1 hsum)).trace := by
  rw [grandCanonicalAlgebraicPartition_eq_coe_grandCanonicalPartitionFunction]
  have hshift := completedFreeHeatOperator_trace_eq_grandCanonicalPartitionFunction_zero
    (fun i => ε i - μ) β hβ hgap
    ((Common.grandCanonicalGibbsSummable_iff_shifted
      (Config := Occupation Mode) ε β μ).1 hsum)
  rw [hshift]
  congr 1
  simpa only [sub_add_cancel, zero_add] using
    (Common.grandCanonicalPartitionFunction_shift_invariant
      (Config := Occupation Mode) (fun i => ε i - μ) β 0 μ).symm

end
end Bosonic
end SecondQuantization

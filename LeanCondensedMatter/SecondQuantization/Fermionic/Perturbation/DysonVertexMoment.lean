import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.Combinatorics.Cumulant.Inversion

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

This file is the seam between the fermionic Dyson partition coefficient, indexed by perturbation
order `ℕ`, and finite-set moment/cumulant combinatorics, indexed by a labelled vertex set `Finset α`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The normalized fermionic Dyson partition coefficient. -/
noncomputable def normalizedDysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) : ℂ :=
  dysonPartitionCoeff ε β V n / freePartitionFunction ε β

omit [LinearOrder Mode] in
/-- Coefficients of the normalized Dyson partition series are the normalized fermionic Dyson
partition coefficients. -/
theorem coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) =
      normalizedDysonPartitionCoeff ε β V n := by
  rw [normalizedDysonPartitionCoeff, PowerSeries.coeff_normalizeByConstantCoeff,
    constantCoeff_dysonPartitionSeries, coeff_dysonPartitionSeries, div_eq_mul_inv]
  exact mul_comm _ _

omit [LinearOrder Mode] in
/-- The normalized Dyson coefficient is the canonical free Gibbs density-state expectation of the
bare Dyson coefficient. This bridge is owned at the perturbative moment layer so diagrammatic
callers do not need to unfold occupation-basis Gibbs formulas. -/
theorem normalizedDysonPartitionCoeff_eq_freeGibbsDensityOperator_expectation
    (ε : Mode → ℝ) (β : ℝ) (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    normalizedDysonPartitionCoeff ε β V n =
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (Common.dysonCoeff (fermionEnergy ε) V n β)) := by
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β := by
    funext m
    rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy]
    push_cast
    ring_nf
  have hZ : Common.traceFock (Common.diagonalEvolution (fermionEnergy ε) (-β)) =
      freePartitionFunction ε β := by
    rw [Common.traceFock_diagonalEvolution_eq_weightSum, ← hw,
      Common.weightSum, freePartitionFunction]
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_eq_trace_div,
    normalizedDysonPartitionCoeff, hZ]
  congr 1

omit [LinearOrder Mode] in
@[simp]
theorem normalizedDysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    normalizedDysonPartitionCoeff ε β V 0 = 1 := by
  rw [normalizedDysonPartitionCoeff, dysonPartitionCoeff_zero,
    div_self (freePartitionFunction_ne_zero ε β)]

/-- The factorial-normalized Dyson vertex moment on a finite vertex set. -/
noncomputable def dysonVertexMoment {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) : ℂ :=
  (S.card.factorial : ℂ) * normalizedDysonPartitionCoeff ε β V S.card

omit [LinearOrder Mode] in
/-- The Dyson vertex moment is the factorial times the canonical free Gibbs density-state
expectation of the bare Dyson coefficient at the corresponding order. -/
theorem dysonVertexMoment_eq_freeGibbsDensityOperator_expectation
    {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) :
    dysonVertexMoment ε β V S =
      (S.card.factorial : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            (Common.dysonCoeff (fermionEnergy ε) V S.card β)) := by
  rw [dysonVertexMoment,
    normalizedDysonPartitionCoeff_eq_freeGibbsDensityOperator_expectation]

omit [LinearOrder Mode] in
@[simp]
theorem dysonVertexMoment_empty {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    dysonVertexMoment ε β V (∅ : Finset α) = 1 := by
  classical
  simp [dysonVertexMoment]

/-- The finite-set cumulant of the Dyson vertex moment. -/
noncomputable def dysonVertexCumulant {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) : ℂ :=
  Finpartition.cumulantFromMoment (dysonVertexMoment ε β V) S

end Fermionic
end SecondQuantization

import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator

set_option linter.style.header false

/-!
# Finite fermionic current insertions as four external fields

A supplied one-body current kernel `j i k` produces the even-parity Fock-space
insertion `J(τ) = ∑ i k, j i k • cᵢ†(τ) cₖ(τ)`. Two such insertions
have four elementary fermionic legs. This file establishes their exact
finite-sum operator and free Gibbs expectation expansions without assuming
a linked-cluster theorem, a disorder average, or a Kubo/Středa limit.

Time ordering is applied to the two **even** current operators, hence uses
the positive exchange sign. Equal-time ordering retains the canonical
half-symmetrized convention of `Common.timeOrderedProduct`.
-/ 

namespace SecondQuantization
namespace Fermionic
namespace Transport

open scoped BigOperators

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- A finite one-body current kernel inserted on occupation Fock space at
imaginary time `τ`. It is a sum of creation-annihilation bilinears; the
kernel is supplied rather than identified with a particular hopping model. -/
noncomputable def bilinearCurrentInsertion (ε : Mode → ℝ) (τ : ℝ)
    (kernel : Mode → Mode → ℂ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  ∑ i : Mode, ∑ j : Mode,
    kernel i j •
      (externalFieldOperator ε τ (.creation i)).comp
        (externalFieldOperator ε τ (.annihilation j))

/-- Multiplying two finite bilinear current insertions is exactly a sum
over four elementary fermionic external-field operators, with the order
inside each composite current kept fixed. No four-field connectedness or
vacuum-bubble cancellation is claimed. -/
theorem bilinearCurrentInsertion_comp_eq_four_fields
    (ε : Mode → ℝ) (τ τ' : ℝ)
    (jx jy : Mode → Mode → ℂ) :
    (bilinearCurrentInsertion ε τ jx).comp
        (bilinearCurrentInsertion ε τ' jy) =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) •
          (((externalFieldOperator ε τ (.creation i)).comp
              (externalFieldOperator ε τ (.annihilation j))).comp
            ((externalFieldOperator ε τ' (.creation k)).comp
              (externalFieldOperator ε τ' (.annihilation l)))) := by
  simp only [bilinearCurrentInsertion, ← Module.End.mul_eq_comp,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Time ordering of two even-parity composite currents. The positive
exchange sign here is not the negative exchange sign of individual
fermionic external fields. -/
noncomputable def timeOrderedBilinearCurrents
    (ε : Mode → ℝ) (jx jy : Mode → Mode → ℂ) (τ τ' : ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.timeOrderedProduct Common.Statistics.boson
    (bilinearCurrentInsertion ε τ jx)
    (bilinearCurrentInsertion ε τ' jy) τ τ'

/-- In the strictly ordered time chamber `τ' < τ`, the two-current
time-ordered product is exactly the four-field operator sum. -/
theorem timeOrderedBilinearCurrents_eq_four_fields_of_gt
    (ε : Mode → ℝ) (jx jy : Mode → Mode → ℂ)
    {τ τ' : ℝ} (h : τ' < τ) :
    timeOrderedBilinearCurrents ε jx jy τ τ' =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) •
          (((externalFieldOperator ε τ (.creation i)).comp
              (externalFieldOperator ε τ (.annihilation j))).comp
            ((externalFieldOperator ε τ' (.creation k)).comp
              (externalFieldOperator ε τ' (.annihilation l)))) := by
  rw [timeOrderedBilinearCurrents,
    Common.timeOrderedProduct_of_gt Common.Statistics.boson _ _ h]
  exact bilinearCurrentInsertion_comp_eq_four_fields ε τ τ' jx jy

/-- The physical finite free-Gibbs density-state expectation of two
current insertions is the corresponding weighted sum of four-field
expectations. This is the unconnected, configuration-free P1 boundary. -/
theorem finiteGibbsBilinearCurrentCurrent_eq_four_fields
    (ε : Mode → ℝ) (β τ τ' : ℝ)
    (jx jy : Mode → Mode → ℂ) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β
        ((bilinearCurrentInsertion ε τ jx).comp
          (bilinearCurrentInsertion ε τ' jy)) =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) *
          Common.finiteGibbsExpectation (fermionEnergy ε) β
            (((externalFieldOperator ε τ (.creation i)).comp
                (externalFieldOperator ε τ (.annihilation j))).comp
              ((externalFieldOperator ε τ' (.creation k)).comp
                (externalFieldOperator ε τ' (.annihilation l)))) := by
  rw [bilinearCurrentInsertion_comp_eq_four_fields]
  simp only [Common.finiteGibbsExpectation, map_sum, map_smul, smul_eq_mul]

end
end Transport
end Fermionic
end SecondQuantization

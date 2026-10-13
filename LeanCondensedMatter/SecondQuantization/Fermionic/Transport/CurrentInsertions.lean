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
  simp only [bilinearCurrentInsertion, ← Module.End.mul_eq_comp]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

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


/-- The reversed imaginary-time chamber contains the opposite ordering of
the two **even** current vertices. No extra fermionic minus sign is attached
to exchanging two composite current operators. -/
theorem timeOrderedBilinearCurrents_eq_four_fields_of_lt
    (ε : Mode → ℝ) (jx jy : Mode → Mode → ℂ)
    {τ τ' : ℝ} (h : τ < τ') :
    timeOrderedBilinearCurrents ε jx jy τ τ' =
      ∑ k : Mode, ∑ l : Mode, ∑ i : Mode, ∑ j : Mode,
        (jy k l * jx i j) •
          (((externalFieldOperator ε τ' (.creation k)).comp
              (externalFieldOperator ε τ' (.annihilation l))).comp
            ((externalFieldOperator ε τ (.creation i)).comp
              (externalFieldOperator ε τ (.annihilation j)))) := by
  rw [timeOrderedBilinearCurrents,
    Common.timeOrderedProduct_of_lt Common.Statistics.boson _ _ h]
  simp only [Common.Statistics.zetaInt_boson, Int.cast_one, one_smul]
  exact bilinearCurrentInsertion_comp_eq_four_fields ε τ' τ jy jx

/-- Equal-time current ordering uses the symmetric convention for **even**
composite insertions, not the antisymmetric elementary-fermion rule. -/
theorem timeOrderedBilinearCurrents_self_time
    (ε : Mode → ℝ) (jx jy : Mode → Mode → ℂ) (τ : ℝ) :
    timeOrderedBilinearCurrents ε jx jy τ τ =
      (2⁻¹ : ℂ) •
        ((bilinearCurrentInsertion ε τ jx).comp
            (bilinearCurrentInsertion ε τ jy) +
          (bilinearCurrentInsertion ε τ jy).comp
            (bilinearCurrentInsertion ε τ jx)) := by
  rw [timeOrderedBilinearCurrents,
    Common.timeOrderedProduct_self_time Common.Statistics.boson]
  simp only [Common.Statistics.zetaInt_boson, Int.cast_one, one_smul]

/-- A normalized free-Gibbs expectation of a current insertion is the
finite weighted sum of its two elementary fermionic fields. -/
theorem finiteGibbsBilinearCurrent_eq_two_fields
    (ε : Mode → ℝ) (β τ : ℝ) (kernel : Mode → Mode → ℂ) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β
        (bilinearCurrentInsertion ε τ kernel) =
      ∑ i : Mode, ∑ j : Mode,
        kernel i j *
          Common.finiteGibbsExpectation (fermionEnergy ε) β
            ((externalFieldOperator ε τ (.creation i)).comp
              (externalFieldOperator ε τ (.annihilation j))) := by
  simp only [bilinearCurrentInsertion, Common.finiteGibbsExpectation,
    map_sum, map_smul, smul_eq_mul]

/-- Connectedness of the two *composite current insertions*:
subtract their product of one-current expectations. This is deliberately
not the connected four-elementary-fermion cumulant. -/
noncomputable def finiteGibbsConnectedBilinearCurrentCorrelation
    (ε : Mode → ℝ) (β τ τ' : ℝ)
    (jx jy : Mode → Mode → ℂ) : ℂ :=
  Common.finiteGibbsExpectation (fermionEnergy ε) β
      ((bilinearCurrentInsertion ε τ jx).comp
        (bilinearCurrentInsertion ε τ' jy)) -
    Common.finiteGibbsExpectation (fermionEnergy ε) β
        (bilinearCurrentInsertion ε τ jx) *
      Common.finiteGibbsExpectation (fermionEnergy ε) β
        (bilinearCurrentInsertion ε τ' jy)

/-- The connected two-current correlator is the four-field sum with only
the **disconnected current-vertex product** removed. Wick contractions
joining the two current vertices survive even if the underlying four
elementary fermion legs are not a single cumulant component. -/
theorem finiteGibbsConnectedBilinearCurrentCorrelation_eq_four_fields
    (ε : Mode → ℝ) (β τ τ' : ℝ)
    (jx jy : Mode → Mode → ℂ) :
    finiteGibbsConnectedBilinearCurrentCorrelation ε β τ τ' jx jy =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) *
          (Common.finiteGibbsExpectation (fermionEnergy ε) β
              (((externalFieldOperator ε τ (.creation i)).comp
                  (externalFieldOperator ε τ (.annihilation j))).comp
                ((externalFieldOperator ε τ' (.creation k)).comp
                  (externalFieldOperator ε τ' (.annihilation l)))) -
            Common.finiteGibbsExpectation (fermionEnergy ε) β
                ((externalFieldOperator ε τ (.creation i)).comp
                  (externalFieldOperator ε τ (.annihilation j))) *
              Common.finiteGibbsExpectation (fermionEnergy ε) β
                ((externalFieldOperator ε τ' (.creation k)).comp
                  (externalFieldOperator ε τ' (.annihilation l)))) := by
  rw [finiteGibbsConnectedBilinearCurrentCorrelation,
    finiteGibbsBilinearCurrentCurrent_eq_four_fields,
    finiteGibbsBilinearCurrent_eq_two_fields,
    finiteGibbsBilinearCurrent_eq_two_fields]
  have hprod :
      (∑ i : Mode, ∑ j : Mode,
        jx i j *
          Common.finiteGibbsExpectation (fermionEnergy ε) β
            ((externalFieldOperator ε τ (.creation i)).comp
              (externalFieldOperator ε τ (.annihilation j)))) *
        (∑ k : Mode, ∑ l : Mode,
          jy k l *
            Common.finiteGibbsExpectation (fermionEnergy ε) β
              ((externalFieldOperator ε τ' (.creation k)).comp
                (externalFieldOperator ε τ' (.annihilation l)))) =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) *
          (Common.finiteGibbsExpectation (fermionEnergy ε) β
              ((externalFieldOperator ε τ (.creation i)).comp
                (externalFieldOperator ε τ (.annihilation j))) *
            Common.finiteGibbsExpectation (fermionEnergy ε) β
              ((externalFieldOperator ε τ' (.creation k)).comp
                (externalFieldOperator ε τ' (.annihilation l)))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hprod]
  simp only [mul_sub, Finset.sum_sub_distrib]

end
end Transport
end Fermionic
end SecondQuantization

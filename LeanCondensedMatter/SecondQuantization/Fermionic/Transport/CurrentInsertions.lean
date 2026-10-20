import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField

set_option linter.style.header false

/-!
# Finite fermionic current insertions as four external fields

A supplied one-body current kernel `j i k` produces the even-parity Fock-space
insertion `J(τ) = ∑ i k, j i k • cᵢ†(τ) cₖ(τ)`. Two such insertions
have four elementary fermionic legs. This file establishes their exact
finite-sum operator and linear-expectation expansions without assuming
a Gibbs state, particle-number ensemble, Wick factorization, a linked-cluster theorem,
a disorder average, or a Kubo/Středa limit.

Time ordering is applied to the two **even** current operators, hence uses
the positive exchange sign. Equal-time ordering retains the canonical
half-symmetrized convention of `Common.timeOrderedProduct`.

The expectation is a complex-linear functional on algebraic Fock endomorphisms.
For physical connected correlations it should be normalized on the identity, but the
finite-sum and subtraction identities below only require linearity. Concrete thermal
states can supply their own functional.
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
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

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

/-- The expectation of two current insertions expands into the weighted sum of four-field
expectations for any complex-linear functional, independently of the statistical ensemble. -/
theorem bilinearCurrentCurrent_expectation_eq_four_fields
    (ε : Mode → ℝ) (τ τ' : ℝ)
    (expectation : (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) →ₗ[ℂ] ℂ)
    (jx jy : Mode → Mode → ℂ) :
    expectation
        ((bilinearCurrentInsertion ε τ jx).comp
          (bilinearCurrentInsertion ε τ' jy)) =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) *
          expectation
            (((externalFieldOperator ε τ (.creation i)).comp
                (externalFieldOperator ε τ (.annihilation j))).comp
              ((externalFieldOperator ε τ' (.creation k)).comp
                (externalFieldOperator ε τ' (.annihilation l)))) := by
  rw [bilinearCurrentInsertion_comp_eq_four_fields]
  simp only [map_sum, map_smul, smul_eq_mul]


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

/-- Any complex-linear expectation of a current insertion is the finite weighted sum of
two elementary fermionic fields. -/
theorem bilinearCurrent_expectation_eq_two_fields
    (ε : Mode → ℝ) (τ : ℝ)
    (expectation : (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) →ₗ[ℂ] ℂ)
    (kernel : Mode → Mode → ℂ) :
    expectation
        (bilinearCurrentInsertion ε τ kernel) =
      ∑ i : Mode, ∑ j : Mode,
        kernel i j *
          expectation
            ((externalFieldOperator ε τ (.creation i)).comp
              (externalFieldOperator ε τ (.annihilation j))) := by
  simp only [bilinearCurrentInsertion, map_sum, map_smul, smul_eq_mul]

/-- Subtract the disconnected product of the two *composite current insertions*.
When the functional is normalized on the identity, this is the connected two-current
correlation (the second cumulant of the composite currents), not the connected cumulant
of four elementary fermionic fields. -/
noncomputable def connectedBilinearCurrentCorrelation
    (ε : Mode → ℝ) (τ τ' : ℝ)
    (expectation : (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) →ₗ[ℂ] ℂ)
    (jx jy : Mode → Mode → ℂ) : ℂ :=
  expectation
      ((bilinearCurrentInsertion ε τ jx).comp
        (bilinearCurrentInsertion ε τ' jy)) -
    expectation
        (bilinearCurrentInsertion ε τ jx) *
      expectation
        (bilinearCurrentInsertion ε τ' jy)

/-- The connected two-current subtraction is a four-field sum with only the
**disconnected current-vertex product** removed. Wick contractions joining the
composite current vertices survive even if four elementary field legs are not
one cumulant component. No Wick assumption is used. -/
theorem connectedBilinearCurrentCorrelation_eq_four_fields
    (ε : Mode → ℝ) (τ τ' : ℝ)
    (expectation : (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) →ₗ[ℂ] ℂ)
    (jx jy : Mode → Mode → ℂ) :
    connectedBilinearCurrentCorrelation ε τ τ' expectation jx jy =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) *
          (expectation
              (((externalFieldOperator ε τ (.creation i)).comp
                  (externalFieldOperator ε τ (.annihilation j))).comp
                ((externalFieldOperator ε τ' (.creation k)).comp
                  (externalFieldOperator ε τ' (.annihilation l)))) -
            expectation
                ((externalFieldOperator ε τ (.creation i)).comp
                  (externalFieldOperator ε τ (.annihilation j))) *
              expectation
                ((externalFieldOperator ε τ' (.creation k)).comp
                  (externalFieldOperator ε τ' (.annihilation l)))) := by
  rw [connectedBilinearCurrentCorrelation,
    bilinearCurrentCurrent_expectation_eq_four_fields,
    bilinearCurrent_expectation_eq_two_fields,
    bilinearCurrent_expectation_eq_two_fields]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end Transport
end Fermionic
end SecondQuantization

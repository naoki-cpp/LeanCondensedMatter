import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TimedField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedTimeOrdering
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Basic

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
For the physical second cumulant it should be normalized on the identity, but the finite-sum
expansions only require linearity. The connected subtraction is the generic
`QuantumTheory.LinearResponse.connectedCorrelation`; it is not a four-fermion cumulant.
Concrete thermal states can supply their own functional.
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

/-- The connected two-current subtraction is a four-field sum with only the
**disconnected current-vertex product** removed. Wick contractions joining the
composite current vertices survive even if four elementary field legs are not
one cumulant component. No Wick assumption is used. -/
theorem connectedCorrelation_bilinearCurrentInsertion_eq_four_fields
    (ε : Mode → ℝ) (τ τ' : ℝ)
    (expectation : (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) →ₗ[ℂ] ℂ)
    (jx jy : Mode → Mode → ℂ) :
    QuantumTheory.LinearResponse.connectedCorrelation expectation
        (bilinearCurrentInsertion ε τ jx)
        (bilinearCurrentInsertion ε τ' jy) =
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
  simp only [QuantumTheory.LinearResponse.connectedCorrelation, Module.End.mul_eq_comp]
  rw [bilinearCurrentCurrent_expectation_eq_four_fields,
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

/-- The fixed elementary field labels of two number-conserving bilinears.
The order is creation, annihilation, creation, annihilation. -/
def pairedCurrentExternalLabels (i j k l : Mode) : Fin 4 → ExternalFieldLabel Mode :=
  fun e => if e = 0 then .creation i else if e = 1 then .annihilation j
    else if e = 2 then .creation k else .annihilation l

/-- The elementary field pair of each composite event, or an unchanged full
interaction vertex. This is the fixed-index integrand before summing the
current matrix elements. -/
noncomputable def pairedCurrentTimedEventOperator {n : ℕ}
    (ε : Mode → ℝ) (τ τ' : ℝ) (i j k l : Mode)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Common.ExternalInsertionTimedEvent 1 n →
      OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .inl e =>
      if e = 0 then
        (externalFieldOperator ε τ (.creation i)).comp
          (externalFieldOperator ε τ (.annihilation j))
      else
        (externalFieldOperator ε τ' (.creation k)).comp
          (externalFieldOperator ε τ' (.annihilation l))
  | .inr v => Common.interactionPicture (fermionEnergy ε)
      (quarticVertexOperator (q v)) (σ v)

omit [Fintype Mode] in
private theorem pairedCurrentTimedEventOperator_eq_blockProduct {n : ℕ}
    (ε : Mode → ℝ) (τ τ' : ℝ) (i j k l : Mode)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : Common.ExternalInsertionTimedEvent 1 n) :
    ((Common.pairedExternalEventBlock event).map
      (externalInsertionTimedEventOperator ε (pairedCurrentExternalLabels i j k l)
        (Common.pairedExternalTimes τ τ') q σ)).prod =
      pairedCurrentTimedEventOperator ε τ τ' i j k l q σ event := by
  cases event with
  | inl e =>
      fin_cases e <;>
        simp [Common.pairedExternalEventBlock, pairedCurrentTimedEventOperator,
          pairedCurrentExternalLabels, Common.pairedExternalTimes,
          externalInsertionTimedEventOperator, Module.End.mul_eq_comp,
          Module.End.one_eq_id]
  | inr v =>
      simp [Common.pairedExternalEventBlock, pairedCurrentTimedEventOperator,
        externalInsertionTimedEventOperator]

omit [Fintype Mode] in
/-- At every perturbative order, the signed four-field interaction-picture
product is the ordinary stable time-ordered product of two even bilinear
events and the full quartic interaction vertices. No fermionic sign is
attached to exchanging the composite events. At equal current times this
identity uses the stable fixed-block order, not symmetric current ordering. -/
theorem externalInsertionMixedTimeOrderedVertexComp_eq_pairedCurrentProduct
    {n : ℕ} (ε : Mode → ℝ) (τ τ' : ℝ) (i j k l : Mode)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    externalInsertionMixedTimeOrderedVertexComp (E := 2) ε
        (pairedCurrentExternalLabels i j k l) (Common.pairedExternalTimes τ τ') q σ =
      ((Common.orderedExternalInsertionTimedEvents (E := 1)
          (fun e => if e = 0 then τ else τ') σ).map
        (pairedCurrentTimedEventOperator ε τ τ' i j k l q σ)).prod := by
  unfold externalInsertionMixedTimeOrderedVertexComp
  rw [Common.orderedExternalInsertionTimedEvents_paired]
  have hsign : externalInsertionMixedAtomicOrderSign (E := 2)
      (Common.pairedExternalTimes τ τ') σ = 1 := by
    simp [externalInsertionMixedAtomicOrderSign,
      Common.externalInsertionStandardToMixedAtomicPositionEquiv_sign_paired]
  rw [hsign, one_smul]
  rw [List.map_flatMap]
  simp only [List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def,
    pairedCurrentTimedEventOperator_eq_blockProduct]


/-- The two full current insertions and unchanged interaction-picture vertices
in the stable composite-event ordering. -/
noncomputable def bilinearCurrentTimedEventOperator {n : ℕ}
    (ε : Mode → ℝ) (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Common.ExternalInsertionTimedEvent 1 n →
      OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .inl e => if e = 0 then bilinearCurrentInsertion ε τ jx
      else bilinearCurrentInsertion ε τ' jy
  | .inr v => Common.interactionPicture (fermionEnergy ε)
      (quarticVertexOperator (q v)) (σ v)

/-- At every perturbative order, the stable product of full currents and
interaction vertices is the current-kernel-weighted sum of the canonical
signed four-field products. Each composite current occurs exactly once.
The equal-current-time convention is stable, not half-symmetrized. -/
theorem bilinearCurrentTimedEventProduct_eq_four_fields {n : ℕ}
    (ε : Mode → ℝ) (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    ((Common.orderedExternalInsertionTimedEvents (E := 1)
        (fun e => if e = 0 then τ else τ') σ).map
      (bilinearCurrentTimedEventOperator ε τ τ' jx jy q σ)).prod =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) • externalInsertionMixedTimeOrderedVertexComp (E := 2) ε
          (pairedCurrentExternalLabels i j k l) (Common.pairedExternalTimes τ τ') q σ := by
  classical
  let times : Fin 2 → ℝ := fun e => if e = 0 then τ else τ'
  let L := Common.orderedExternalInsertionTimedEvents (E := 1) times σ
  let op (X Y : Module.End ℂ (OccupationFock Mode)) :
      Common.ExternalInsertionTimedEvent 1 n → Module.End ℂ (OccupationFock Mode)
    | .inl e => if e = 0 then X else Y
    | .inr v => Common.interactionPicture (fermionEnergy ε)
        (quarticVertexOperator (q v)) (σ v)
  let x (p : Mode × Mode) := (externalFieldOperator ε τ (.creation p.1)).comp
    (externalFieldOperator ε τ (.annihilation p.2))
  let y (p : Mode × Mode) := (externalFieldOperator ε τ' (.creation p.1)).comp
    (externalFieldOperator ε τ' (.annihilation p.2))
  let wx (p : Mode × Mode) := jx p.1 p.2
  let wy (p : Mode × Mode) := jy p.1 p.2
  let X := bilinearCurrentInsertion ε τ jx
  let Y := bilinearCurrentInsertion ε τ' jy
  have hn : L.Nodup := Common.orderedExternalInsertionTimedEvents_nodup (E := 1) times σ
  have hm (e : Common.ExternalInsertionTimedEvent 1 n) : e ∈ L :=
    Common.orderedExternalInsertionTimedEvents_all_mem (E := 1) times σ e
  have hx : X = ∑ p : Mode × Mode, wx p • x p := by
    simp only [X, bilinearCurrentInsertion, Fintype.sum_prod_type, wx, x]
  have hy : Y = ∑ p : Mode × Mode, wy p • y p := by
    simp only [Y, bilinearCurrentInsertion, Fintype.sum_prod_type, wy, y]
  have hfirst : (L.map (op X Y)).prod =
      ∑ p : Mode × Mode, wx p • (L.map (op (x p) Y)).prod := by
    refine ScalarExchange.list_prod_map_weighted_sum_at L (.inl 0) (hm _) hn wx
      (op X Y) (fun p => op (x p) Y) ?_ ?_
    · exact hx
    · intro p e he
      cases e with
      | inl e =>
          fin_cases e
          · exact (he rfl).elim
          · rfl
      | inr v => rfl
  have hsecond (p : Mode × Mode) : (L.map (op (x p) Y)).prod =
      ∑ r : Mode × Mode, wy r • (L.map (op (x p) (y r))).prod := by
    refine ScalarExchange.list_prod_map_weighted_sum_at L (.inl 1) (hm _) hn wy
      (op (x p) Y) (fun r => op (x p) (y r)) ?_ ?_
    · exact hy
    · intro r e he
      cases e with
      | inl e =>
          fin_cases e
          · rfl
          · exact (he rfl).elim
      | inr v => rfl
  have hexp : (L.map (op X Y)).prod =
      ∑ p : Mode × Mode, ∑ r : Mode × Mode,
        (wx p * wy r) • (L.map (op (x p) (y r))).prod := by
    rw [hfirst]
    simp_rw [hsecond, Finset.smul_sum, smul_smul]
  simpa only [Fintype.sum_prod_type, externalInsertionMixedTimeOrderedVertexComp_eq_pairedCurrentProduct]
    using hexp

/-- The weighted four-field identity holds for every complex-linear expectation,
in particular the free-Gibbs expectation in the vertex Dyson integrand. -/
theorem bilinearCurrentTimedEventProduct_expectation_eq_four_fields {n : ℕ}
    (ε : Mode → ℝ) (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (expectation : (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) →ₗ[ℂ] ℂ) :
    expectation (((Common.orderedExternalInsertionTimedEvents (E := 1)
        (fun e => if e = 0 then τ else τ') σ).map
      (bilinearCurrentTimedEventOperator ε τ τ' jx jy q σ)).prod) =
      ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) * expectation
          (externalInsertionMixedTimeOrderedVertexComp (E := 2) ε
            (pairedCurrentExternalLabels i j k l) (Common.pairedExternalTimes τ τ') q σ) := by
  rw [bilinearCurrentTimedEventProduct_eq_four_fields]
  simp only [map_sum, map_smul, smul_eq_mul]

end
end Transport
end Fermionic
end SecondQuantization

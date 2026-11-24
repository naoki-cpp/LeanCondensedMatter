import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.Analysis.ScalarExchange.Basic

set_option linter.style.header false

/-!
# Fermionic realization of mixed event order

`SecondQuantization.Common` owns the statistics-independent event type, stable time order, sorted
event list, and event positions. This module supplies the fermionic operator represented by each
event, the atomic permutation sign and the mixed interaction-picture product. The two-point
operators specialize the arbitrary-external product, including its chemical-potential transport.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- Fermionic sign of the permutation from fixed flattened atomic order to mixed-time atomic order. -/
noncomputable def externalInsertionMixedAtomicOrderSign {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  ((Equiv.Perm.sign
    (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) : ℤ) : ℂ)


/-- The atomic ordering sign is independent of all interaction times, even
when their order changes or they coincide. Only external inversions contribute. -/
theorem externalInsertionMixedAtomicOrderSign_eq_of_externalTimes {E n m : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) (υ : Fin m → ℝ) :
    externalInsertionMixedAtomicOrderSign externalTime σ =
      externalInsertionMixedAtomicOrderSign externalTime υ := by
  simp only [externalInsertionMixedAtomicOrderSign,
    externalInsertionStandardToMixedAtomicPositionEquiv_sign]

/-- Signed mixed-time-ordered interaction-picture vertex product, with the fermionic sign from
restoring the fixed external/interaction atomic order. -/
noncomputable def externalInsertionMixedTimeOrderedVertexComp {E n : ℕ}
    (ε : Mode → ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  externalInsertionMixedAtomicOrderSign externalTime σ •
    ((orderedExternalInsertionTimedEvents externalTime σ).map
      (externalInsertionTimedEventOperator ε externalLabel externalTime q σ)).prod

/-- A uniform energy shift contributes exactly the product of the external field
factors. The number-conserving interaction vertices and the ordering sign are unchanged. -/
theorem externalInsertionMixedTimeOrderedVertexComp_eq_shiftedDispersion {E n : ℕ}
    (ε : Mode → ℝ) (μ : ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    externalInsertionMixedTimeOrderedVertexComp ε externalLabel externalTime q σ =
      externalFieldFamilyChemicalPotentialFactor μ externalLabel externalTime •
        externalInsertionMixedTimeOrderedVertexComp
          (fun k => ε k - μ) externalLabel externalTime q σ := by
  let a : ExternalInsertionTimedEvent E n → ℂ
    | .inl e => externalFieldChemicalPotentialFactor μ (externalTime e) (externalLabel e)
    | .inr _ => 1
  have hevent (e : ExternalInsertionTimedEvent E n) :
      externalInsertionTimedEventOperator ε externalLabel externalTime q σ e =
        a e • externalInsertionTimedEventOperator
          (fun k => ε k - μ) externalLabel externalTime q σ e := by
    cases e with
    | inl e =>
        exact externalFieldOperator_eq_shiftedDispersion ε μ
          (externalTime e) (externalLabel e)
    | inr v =>
        change Common.interactionPicture (fermionEnergy ε) (quarticVertexOperator (q v))
          (σ v) = (1 : ℂ) • Common.interactionPicture
            (fermionEnergy (fun k => ε k - μ)) (quarticVertexOperator (q v)) (σ v)
        rw [one_smul, interactionPicture_quarticVertexOperator_sub_chemicalPotential ε μ]
  have hscalar :
      ((orderedExternalInsertionTimedEvents externalTime σ).map a).prod =
        externalFieldFamilyChemicalPotentialFactor μ externalLabel externalTime := by
    rw [prod_orderedExternalInsertionTimedEvents, Fintype.prod_sum_type]
    simp [a, externalFieldFamilyChemicalPotentialFactor]
  unfold externalInsertionMixedTimeOrderedVertexComp
  rw [funext hevent]
  rw [ScalarExchange.list_prod_map_smul, hscalar,
    smul_comm (externalInsertionMixedAtomicOrderSign externalTime σ)]

/-- Fermionic operator represented by one Common mixed event: an external field for a distinguished
event and an interaction-picture quartic vertex for an interaction event. -/
noncomputable def twoPointTimedEventOperator {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  externalInsertionTimedEventOperator (E := 1) ε (twoPointExternalLabels i j)
    (twoPointExternalTimes τ τ') q σ

@[simp]
theorem twoPointTimedEventOperator_external_zero {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl 0) =
      externalFieldOperator ε τ (.annihilation i) := by
  simp [twoPointTimedEventOperator, externalInsertionTimedEventOperator]

@[simp]
theorem twoPointTimedEventOperator_external_one {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl 1) =
      externalFieldOperator ε τ' (.creation j) := by
  simp [twoPointTimedEventOperator, externalInsertionTimedEventOperator]

@[simp]
theorem twoPointTimedEventOperator_interaction {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) (v : Fin n) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inr v) =
      Common.interactionPicture (fermionEnergy ε) (quarticVertexOperator (q v)) (σ v) := rfl

/-- Exchange prefactor from reversing the two odd fermionic external fields in the Common stable
mixed-event order. -/
noncomputable def twoPointExternalOrderSign (τ τ' : ℝ) : ℂ :=
  @ite ℂ (τ < τ') (Classical.propDecidable _)
    (Common.Statistics.fermion.zetaInt : ℂ) 1

/-- Fermionic mixed time-ordered operator product: compose operators in the Common mixed-event order
and multiply by the external-field exchange sign. -/
noncomputable def mixedTimeOrderedVertexComp {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  twoPointExternalOrderSign τ τ' •
    List.prod ((orderedTwoPointTimedEvents τ τ' σ).map
      (twoPointTimedEventOperator ε i j τ τ' q σ))

/-- The general atomic-order sign specializes to the two-point external-field
exchange sign, independently of the interaction times. -/
theorem externalInsertionMixedAtomicOrderSign_twoPoint
    {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    externalInsertionMixedAtomicOrderSign (E := 1) (twoPointExternalTimes τ τ') σ =
      twoPointExternalOrderSign τ τ' := by
  classical
  rw [externalInsertionMixedAtomicOrderSign,
    externalInsertionStandardToMixedAtomicPositionEquiv_sign_twoPoint]
  by_cases h : τ < τ'
  · simp [h, twoPointExternalOrderSign, Common.Statistics.zetaInt]
  · simp [h, twoPointExternalOrderSign]

/-- The two physical mixed vertex products coincide, including at equal times.
Both definitions use the same event operators and the same stable order. -/
theorem mixedTimeOrderedVertexComp_eq_externalInsertion
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      externalInsertionMixedTimeOrderedVertexComp (E := 1) ε
        (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') q σ := by
  simp only [mixedTimeOrderedVertexComp, externalInsertionMixedTimeOrderedVertexComp,
    orderedTwoPointTimedEvents_eq_externalInsertion,
    externalInsertionMixedAtomicOrderSign_twoPoint, twoPointTimedEventOperator]

/-- The external-field factor relating physical-H evolution to evolution at the
effective grand-canonical dispersion ε − μ. -/
noncomputable def twoPointChemicalPotentialFactor (μ τ τ' : ℝ) : ℂ :=
  Complex.exp ((μ : ℂ) * ((τ' : ℂ) - (τ : ℂ)))

/-- The two-point chemical potential factor is exactly the product of the
two physical external-field factors. -/
theorem externalFieldFamilyChemicalPotentialFactor_twoPoint {M : Type*}
    (μ τ τ' : ℝ) (i j : M) :
    externalFieldFamilyChemicalPotentialFactor μ
      (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') =
        twoPointChemicalPotentialFactor μ τ τ' := by
  rw [externalFieldFamilyChemicalPotentialFactor, Fin.prod_univ_two,
    twoPointExternalLabels_zero, twoPointExternalLabels_one,
    twoPointExternalTimes_zero, twoPointExternalTimes_one]
  change Complex.exp (-(τ : ℂ) * (μ : ℂ)) * Complex.exp ((τ' : ℂ) * (μ : ℂ)) = _
  rw [← Complex.exp_add, twoPointChemicalPotentialFactor]
  congr 1
  ring

/-- Shifting the free dispersion by μ changes the complete mixed-event operator
product only by the two external field factors. In particular, interaction times
and equal-time conventions are unchanged. -/
theorem mixedTimeOrderedVertexComp_eq_shiftedDispersion
    {n : ℕ} (ε : Mode → ℝ) (μ : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      twoPointChemicalPotentialFactor μ τ τ' •
        mixedTimeOrderedVertexComp (fun k => ε k - μ) i j τ τ' q σ := by
  rw [mixedTimeOrderedVertexComp_eq_externalInsertion,
    externalInsertionMixedTimeOrderedVertexComp_eq_shiftedDispersion,
    externalFieldFamilyChemicalPotentialFactor_twoPoint,
    ← mixedTimeOrderedVertexComp_eq_externalInsertion]

set_option linter.unusedSimpArgs false in
private theorem orderedTwoPointTimedEvents_zero_of_gt (σ : Fin 0 → ℝ)
    {τ τ' : ℝ} (h : τ' < τ) :
    orderedTwoPointTimedEvents τ τ' σ = [Sum.inl 0, Sum.inl 1] := by
  have hnot : ¬ τ < τ' := not_lt_of_ge h.le
  have hne : τ' ≠ τ := ne_of_lt h
  have hnotle : ¬ τ ≤ τ' := not_le_of_gt h
  simp [orderedTwoPointTimedEvents, twoPointInteractionEventList, List.insertionSort,
    List.orderedInsert, twoPointTimedEventBeforeOrEqual, twoPointTimedEventTime,
    stableTimedEventBeforeOrEqual_iff, twoPointTimedEventRank, hnot, hne, hnotle]

set_option linter.unusedSimpArgs false in
private theorem orderedTwoPointTimedEvents_zero_of_lt (σ : Fin 0 → ℝ)
    {τ τ' : ℝ} (h : τ < τ') :
    orderedTwoPointTimedEvents τ τ' σ = [Sum.inl 1, Sum.inl 0] := by
  simp [orderedTwoPointTimedEvents, twoPointInteractionEventList, List.insertionSort,
    List.orderedInsert, twoPointTimedEventBeforeOrEqual, twoPointTimedEventTime,
    stableTimedEventBeforeOrEqual_iff, twoPointTimedEventRank, h, h.le, h.ne]

theorem mixedTimeOrderedVertexComp_zero_of_gt (ε : Mode → ℝ) (i j : Mode)
    (q : Fin 0 → QuarticVertexLabel Mode) (σ : Fin 0 → ℝ) {τ τ' : ℝ} (h : τ' < τ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ = twoPointTimeOrderedProduct ε i j τ τ' := by
  rw [twoPointTimeOrderedProduct_of_gt ε i j h, mixedTimeOrderedVertexComp,
    orderedTwoPointTimedEvents_zero_of_gt σ h]
  simp [twoPointExternalOrderSign, not_lt_of_ge h.le, Module.End.mul_eq_comp, Module.End.one_eq_id]

theorem mixedTimeOrderedVertexComp_zero_of_lt (ε : Mode → ℝ) (i j : Mode)
    (q : Fin 0 → QuarticVertexLabel Mode) (σ : Fin 0 → ℝ) {τ τ' : ℝ} (h : τ < τ') :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ = twoPointTimeOrderedProduct ε i j τ τ' := by
  rw [twoPointTimeOrderedProduct_of_lt ε i j h, mixedTimeOrderedVertexComp,
    orderedTwoPointTimedEvents_zero_of_lt σ h]
  simp [twoPointExternalOrderSign, h, Module.End.mul_eq_comp, Module.End.one_eq_id]

end Fermionic
end SecondQuantization

import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointImaginaryTimeOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ExternalField
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic

set_option linter.style.header false

/-!
# Fermionic realization of the mixed two-point event order

`SecondQuantization.Common` owns the statistics-independent event type, stable time order, sorted
event list, and event positions. This module supplies the fermionic operator represented by each
event and the exchange sign contributed when the two odd external fields are reversed. Moving an
external field past a quartic interaction vertex contributes no sign because the quartic vertex is
even.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode]

/-- Fermionic operator represented by one Common mixed event: an external field for a distinguished
event and an interaction-picture quartic vertex for an interaction event. -/
noncomputable def twoPointTimedEventOperator {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .inl e => externalFieldOperator ε (twoPointExternalTimes τ τ' e)
      (twoPointExternalLabels i j e)
  | .inr v => Common.interactionPicture (fermionEnergy ε) (quarticVertexOperator (q v)) (σ v)

@[simp]
theorem twoPointTimedEventOperator_external_zero {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl 0) =
      externalFieldOperator ε τ (.annihilation i) := by
  simp [twoPointTimedEventOperator]

@[simp]
theorem twoPointTimedEventOperator_external_one {n : ℕ} (ε : Mode → ℝ) (i j : Mode)
    (τ τ' : ℝ) (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    twoPointTimedEventOperator ε i j τ τ' q σ (Sum.inl 1) =
      externalFieldOperator ε τ' (.creation j) := by
  simp [twoPointTimedEventOperator]

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

/-- A uniform chemical-potential shift leaves the imaginary-time evolution of a
number-conserving quartic vertex unchanged. -/
theorem interactionPicture_quarticVertexOperator_sub_chemicalPotential
    (ε : Mode → ℝ) (μ τ : ℝ) (q : QuarticVertexLabel Mode) :
    Common.interactionPicture (fermionEnergy ε) (quarticVertexOperator q) τ =
      Common.interactionPicture (fermionEnergy (fun k => ε k - μ))
        (quarticVertexOperator q) τ := by
  have hevolve (η : Mode → ℝ) :
      Common.interactionPicture (fermionEnergy η) (quarticVertexOperator q) τ =
        Common.quarticVertexTimeFactor η q τ • quarticVertexOperator q :=
    Common.heisenbergEvolve_quarticVertexOperator (fermionEnergy η) η
      create annihilate q τ (imaginaryTimeEvolve_create η τ)
      (imaginaryTimeEvolve_annihilate η τ)
  have hshift : Common.quarticVertexEnergyShift (fun k => ε k - μ) q =
      Common.quarticVertexEnergyShift ε q := by
    unfold Common.quarticVertexEnergyShift
    ring
  rw [hevolve ε, hevolve (fun k => ε k - μ)]
  simp only [Common.quarticVertexTimeFactor, hshift]

/-- The external-field factor relating physical-H evolution to evolution at the
effective grand-canonical dispersion ε − μ. -/
noncomputable def twoPointChemicalPotentialFactor (μ τ τ' : ℝ) : ℂ :=
  Complex.exp ((μ : ℂ) * ((τ' : ℂ) - (τ : ℂ)))

/-- Shifting the free dispersion by μ changes the complete mixed-event operator
product only by the two external field factors. In particular, interaction times
and equal-time conventions are unchanged. -/
theorem mixedTimeOrderedVertexComp_eq_shiftedDispersion
    {n : ℕ} (ε : Mode → ℝ) (μ : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      twoPointChemicalPotentialFactor μ τ τ' •
        mixedTimeOrderedVertexComp (fun k => ε k - μ) i j τ τ' q σ := by
  let a : TwoPointTimedEvent n → ℂ := fun e =>
    match e with
    | .inl e => if e = 0 then Complex.exp (-(τ : ℂ) * (μ : ℂ))
        else Complex.exp ((τ' : ℂ) * (μ : ℂ))
    | .inr _ => 1
  have hevent (e : TwoPointTimedEvent n) :
      twoPointTimedEventOperator ε i j τ τ' q σ e =
        a e • twoPointTimedEventOperator (fun k => ε k - μ) i j τ τ' q σ e := by
    rcases e with e | v
    · fin_cases e
      · change externalFieldOperator ε τ (.annihilation i) =
          Complex.exp (-(τ : ℂ) * (μ : ℂ)) •
            externalFieldOperator (fun k => ε k - μ) τ (.annihilation i)
        rw [externalFieldOperator_annihilation_eq_smul,
          externalFieldOperator_annihilation_eq_smul, smul_smul, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
      · change externalFieldOperator ε τ' (.creation j) =
          Complex.exp ((τ' : ℂ) * (μ : ℂ)) •
            externalFieldOperator (fun k => ε k - μ) τ' (.creation j)
        rw [externalFieldOperator_creation_eq_smul,
          externalFieldOperator_creation_eq_smul, smul_smul, ← Complex.exp_add]
        congr 1
        congr 1
        push_cast
        ring
    · simp only [twoPointTimedEventOperator_interaction, a, one_smul]
      exact interactionPicture_quarticVertexOperator_sub_chemicalPotential ε μ (σ v) (q v)
  have hprod (l : List (TwoPointTimedEvent n)) :
      (l.map (twoPointTimedEventOperator ε i j τ τ' q σ)).prod =
        (l.map a).prod •
          (l.map (twoPointTimedEventOperator (fun k => ε k - μ) i j τ τ' q σ)).prod := by
    induction l with
    | nil => simp
    | cons e l ih =>
        simp only [List.map_cons, List.prod_cons, hevent e, ih,
          Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
        rw [mul_comm (l.map a).prod (a e)]
  have htail : ((twoPointInteractionEventList n).map a).prod = 1 := by
    rw [twoPointInteractionEventList, List.map_ofFn]
    simp [Function.comp_def, a]
  have hscalar : ((orderedTwoPointTimedEvents τ τ' σ).map a).prod =
      twoPointChemicalPotentialFactor μ τ τ' := by
    rw [((orderedTwoPointTimedEvents_perm τ τ' σ).map a).prod_eq]
    change Complex.exp (-(τ : ℂ) * (μ : ℂ)) *
      (Complex.exp ((τ' : ℂ) * (μ : ℂ)) * ((twoPointInteractionEventList n).map a).prod) =
        twoPointChemicalPotentialFactor μ τ τ'
    rw [htail, mul_one, ← Complex.exp_add, twoPointChemicalPotentialFactor]
    congr 1
    ring
  unfold mixedTimeOrderedVertexComp
  rw [hprod, hscalar, smul_comm (twoPointExternalOrderSign τ τ')]

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

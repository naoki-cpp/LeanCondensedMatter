import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.PhysicalDysonIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Time-ordered external fields and quartic interaction vertices

The canonical stable mixed-event ordering is interpreted as an ordered product
of full interaction-picture quartic vertices and individually evolved external
fields. Expanding every quartic vertex into its four canonical legs recovers
the mixed-time atomic operator product used in the physical Wick expansion.

The fermionic sign is the permutation of *all* atomic legs from fixed
external-first order to mixed-time order; four-leg interaction vertices are
even. The stable event ranking resolves equal-time ties.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- One external field or one full quartic interaction-picture vertex. -/
noncomputable def externalInsertionTimedEventOperator {E n : ℕ}
    (ε : Mode → ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    ExternalInsertionTimedEvent E n →
      OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .inl e => externalFieldOperator ε (externalTime e) (externalLabel e)
  | .inr v => interactionPicture ε (quarticVertexOperator (q v)) (σ v)

/-- Physical mixed-time-ordered vertex product, with the fermionic sign from
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

/-- One event flattened into the atomic evolved operators in its canonical
external-leg or quartic-leg order. -/
private noncomputable def externalInsertionTimedEventAtomicOperators {E n : ℕ}
    (ε : Mode → ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E n) :
    List (OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :=
  (externalInsertionTimedEventAtomicLegs event).map
    (fun leg => timedFieldOperator ε
      (orderedExternalInsertionLegField externalLabel externalTime q σ leg))

private theorem prod_externalInsertionTimedEventAtomicOperators {E n : ℕ}
    (ε : Mode → ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E n) :
    (externalInsertionTimedEventAtomicOperators
      ε externalLabel externalTime q σ event).prod =
    externalInsertionTimedEventOperator ε externalLabel externalTime q σ event := by
  cases event with
  | inl e =>
      simp [externalInsertionTimedEventAtomicOperators,
        externalInsertionTimedEventAtomicLegs, externalInsertionTimedEventOperator,
        orderedExternalInsertionLegField, orderedExternalInsertionLegTime,
        orderedExternalInsertionLegFieldLabel, timedFieldOperator,
        Module.End.mul_eq_comp, Module.End.one_eq_id]
  | inr v =>
      have hlegs :
          externalInsertionTimedEventAtomicOperators
              ε externalLabel externalTime q σ (.inr v) =
            List.ofFn (fun l : Fin 4 =>
              imaginaryTimeEvolve ε (σ v) (quarticLocalLegOperator (q v) l)) := by
        unfold externalInsertionTimedEventAtomicOperators
          externalInsertionTimedEventAtomicLegs
        rw [List.map_ofFn]
        apply congrArg List.ofFn
        funext l
        simpa only [orderedExternalInsertionLegField,
          orderedExternalInsertionLegTime, orderedExternalInsertionLegFieldLabel,
          quarticLocalLegOperator] using
          (timedFieldOperator_quarticLocalLeg ε (σ v)
            (Common.quarticLocalLeg (q v) l))
      rw [hlegs]
      change
        (List.ofFn (fun l : Fin 4 =>
          Common.heisenbergEvolve (fermionEnergy ε) (σ v)
            (Common.quarticLocalLegOperator create annihilate (q v) l))).prod =
          Common.heisenbergEvolve (fermionEnergy ε) (σ v)
            (Common.quarticVertexOperator create annihilate (q v))
      exact (Common.heisenbergEvolve_quarticVertexOperator_eq_prod
        (fermionEnergy ε) create annihilate (q v) (σ v)).symm

/-- The flattened time-ordered event list agrees with the established
mixed-time atomic field family, including all equal-time conventions. -/
private theorem externalInsertionMixedAtomicOperators_eq_ofFn {E n : ℕ}
    (ε : Mode → ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).flatMap
        (externalInsertionTimedEventAtomicOperators
          ε externalLabel externalTime q σ) =
      List.ofFn (fun p : Fin (2 * (2 * n + E)) =>
        timedFieldOperator ε
          (externalInsertionMixedTimeOrderedAtomicFieldFamily
            externalLabel externalTime q σ p)) := by
  let f : OrderedExternalInsertionLeg E n →
      OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
    fun leg => timedFieldOperator ε
      (orderedExternalInsertionLegField externalLabel externalTime q σ leg)
  change
    (orderedExternalInsertionTimedEvents externalTime σ).flatMap
        (fun event => (externalInsertionTimedEventAtomicLegs event).map f) =
      List.ofFn (fun p => f
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p))
  rw [← List.map_flatMap]
  rw [externalInsertionMixedTimeOrderedAtomicLegs_eq_ofFn]
  rw [List.map_ofFn]

/-- **Vertex-to-atomic operator identity.** The mixed time-ordered product
of full interaction-picture vertices and external fields is exactly the
fermionic atomic-order sign times the product of its mixed-time atomic fields. -/
theorem externalInsertionMixedTimeOrderedVertexComp_eq_atomicProduct {E n : ℕ}
    (ε : Mode → ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    externalInsertionMixedTimeOrderedVertexComp ε externalLabel externalTime q σ =
      externalInsertionMixedAtomicOrderSign externalTime σ •
        (List.ofFn (fun p : Fin (2 * (2 * n + E)) =>
          timedFieldOperator ε
            (externalInsertionMixedTimeOrderedAtomicFieldFamily
              externalLabel externalTime q σ p))).prod := by
  rw [← externalInsertionMixedAtomicOperators_eq_ofFn
    ε externalLabel externalTime q σ]
  simp only [externalInsertionMixedTimeOrderedVertexComp,
    List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def,
    prod_externalInsertionTimedEventAtomicOperators]

end Fermionic
end SecondQuantization

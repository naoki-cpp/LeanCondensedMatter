import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.MixedAtomicDysonIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.CauchySeries

set_option linter.style.header false

/-!
# Interaction-picture quartic-vertex Dyson expansion

The canonical stable mixed-event ordering is interpreted as an ordered product
of full interaction-picture quartic vertices and individually evolved external
fields. Expanding every quartic vertex into its four canonical legs recovers
the mixed-time atomic operator product used in the free-Gibbs Wick expansion.
The fermionic sign is the permutation of all atomic legs from fixed external-first
order to mixed-time order; four-leg interaction vertices are even, and stable
event ranking resolves equal-time ties.

The interaction-picture perturbation expansion is expressed directly through
these mixed-time-ordered products in the free Gibbs state. Their ordering signs
and time integrations agree with the finite Wick-diagram Dyson coefficients.
The resulting formal series need not converge analytically, and removing
pure-vacuum components does not force different external insertions to lie in
the same connected component.
-/

namespace SecondQuantization
namespace Fermionic

open Common

section VertexProduct

variable {Mode : Type*} [LinearOrder Mode]

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
        change
          timedFieldOperator ε
            ⟨σ v, quarticLocalLegExternalFieldLabel (Common.quarticLocalLeg (q v) l)⟩ =
          imaginaryTimeEvolve ε (σ v)
            (Common.quarticLocalLegOperator create annihilate (q v) l)
        exact timedFieldOperator_quarticLocalLeg ε (σ v)
          (Common.quarticLocalLeg (q v) l)
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
  change
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).map f =
      List.ofFn (fun p => f
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p))
  rw [externalInsertionMixedTimeOrderedAtomicLegs_eq_ofFn]
  rw [List.map_ofFn]
  rfl

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

end VertexProduct

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- At μ = 0, the interaction-picture vertex Dyson coefficient equals the
integrated Wick-diagram coefficient at each finite perturbative order. -/
theorem externalInsertionVertexDysonCoefficient_eq_externalInsertionDysonCoefficient
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionVertexDysonCoefficient
        ε β 0 g externalLabel externalTime n =
      externalInsertionDysonCoefficient
        ε β g externalLabel externalTime n := by
  calc
    externalInsertionVertexDysonCoefficient ε β 0 g externalLabel externalTime n =
        externalInsertionMixedAtomicDysonCoefficient
          ε β 0 g externalLabel externalTime n := by
      unfold externalInsertionVertexDysonCoefficient
        externalInsertionMixedAtomicDysonCoefficient
      apply intervalIntegral.orderedSimplexIntegral_congr
      intro σ
      apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [externalInsertionMixedTimeOrderedVertexComp_eq_atomicProduct]
      simp only [sub_zero, Common.finiteGibbsExpectation, map_smul, smul_eq_mul]
      ring
    _ = externalInsertionDysonCoefficient
          ε β g externalLabel externalTime n :=
      externalInsertionMixedAtomicDysonCoefficient_eq_externalInsertionDysonCoefficient
        ε β g externalLabel externalTime n

/-- Formal series of explicit-μ free-Gibbs interaction-picture vertex Dyson coefficients. -/
noncomputable def externalInsertionVertexDysonSeries {E : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (externalInsertionVertexDysonCoefficient
    ε β μ g externalLabel externalTime)

/-- Series-level physical-H transport at arbitrary chemical potential. -/
theorem externalInsertionVertexDysonSeries_eq_shiftedDispersion {E : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionVertexDysonSeries ε β μ g externalLabel externalTime =
      PowerSeries.C (externalFieldFamilyChemicalPotentialFactor μ externalLabel externalTime) *
        externalInsertionVertexDysonSeries
          (fun k => ε k - μ) β 0 g externalLabel externalTime := by
  ext n
  simp only [PowerSeries.coeff_C_mul, externalInsertionVertexDysonSeries, PowerSeries.coeff_mk]
  exact externalInsertionVertexDysonCoefficient_eq_shiftedDispersion
    ε β μ g externalLabel externalTime n

/-- At μ = 0, the interaction-picture vertex Dyson formal series is the already-proved
diagrammatic external-insertion series. -/
theorem externalInsertionVertexDysonSeries_eq_externalInsertionDysonSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionVertexDysonSeries ε β 0 g externalLabel externalTime =
      externalInsertionDysonSeries ε β g externalLabel externalTime := by
  ext n
  simp only [externalInsertionVertexDysonSeries, externalInsertionDysonSeries,
    PowerSeries.coeff_mk]
  exact externalInsertionVertexDysonCoefficient_eq_externalInsertionDysonCoefficient
    ε β g externalLabel externalTime n

/-- At μ = 0, the interaction-picture vertex Dyson formal series contains precisely the
vacuum-free external contribution times the normalized vacuum partition
series. Externally supported but mutually disconnected components remain. -/
theorem externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionVertexDysonSeries ε β 0 g externalLabel externalTime =
      vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) := by
  rw [externalInsertionVertexDysonSeries_eq_externalInsertionDysonSeries]
  exact externalInsertionDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    ε β hβ g externalLabel externalTime

/-- The physical-H vertex series at arbitrary μ factors into its effective-dispersion
vacuum-free diagram series (with the physical external-field scalar) and normalized
grand-canonical vacuum series. No new Wick or shuffle expansion is required. -/
theorem externalInsertionVertexDysonSeries_eq_shiftedVacuumFree_mul_normalizedDysonPartitionSeries
    {E : ℕ} (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionVertexDysonSeries ε β μ g externalLabel externalTime =
      (PowerSeries.C (externalFieldFamilyChemicalPotentialFactor μ externalLabel externalTime) *
        vacuumFreeExternalInsertionDysonSeries (fun k => ε k - μ) β g
          externalLabel externalTime) *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy (fun k => ε k - μ)) β
            (quarticInteraction g)) := by
  rw [externalInsertionVertexDysonSeries_eq_shiftedDispersion,
    externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
      (fun k => ε k - μ) β hβ, mul_assoc]

end Fermionic
end SecondQuantization

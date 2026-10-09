import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option linter.style.header false

/-!
# Finite signatures for mixed-order chambers

Mixed-order chambers for two-point and arbitrary even external insertions are determined by
finitely many strict event-time comparisons. Their signature fibers are Borel measurable. This
construction depends only on event ordering and not on particle statistics.
-/

namespace SecondQuantization
namespace Common

/-! ## Finite strict-comparison signatures -/

/-- The truth table of all strict time comparisons in a finite event family. -/
private noncomputable def strictOrderSignature
    {Event X : Type*} [Fintype Event]
    (time : X → Event → ℝ) (x : X) : Finset (Event × Event) :=
  Finset.univ.filter fun p => time x p.1 < time x p.2

private theorem strictOrderSignature_eq_iff
    {Event X : Type*} [Fintype Event]
    (time : X → Event → ℝ) (x y : X) :
    strictOrderSignature time x = strictOrderSignature time y ↔
      ∀ a b : Event, (time x a < time x b ↔ time y a < time y b) := by
  classical
  constructor
  · intro h a b
    have hp :
        ((a, b) ∈ strictOrderSignature time x) ↔
          ((a, b) ∈ strictOrderSignature time y) := by
      rw [h]
    simpa [strictOrderSignature] using hp
  · intro h
    ext p
    rcases p with ⟨a, b⟩
    simpa [strictOrderSignature] using h a b

/-- A mixed family contains fixed external events and variable interaction times. -/
private theorem continuous_sumEventTime {External : Type*} {n : ℕ}
    (externalTime : External → ℝ) (event : External ⊕ Fin n) :
    Continuous (fun σ : Fin n → ℝ => Sum.elim externalTime σ event) := by
  cases event with
  | inl _ => exact continuous_const
  | inr v => exact continuous_apply v

private theorem measurable_strictOrderSignature
    {Event X : Type*} [Fintype Event] [MeasurableSpace X]
    (time : X → Event → ℝ)
    (htime : ∀ a : Event, Measurable (fun x : X => time x a)) :
    Measurable (strictOrderSignature time) := by
  rw [measurable_finset_iff_measurable_set, measurable_set_iff]
  rintro ⟨a, b⟩
  apply measurable_to_prop
  simpa [strictOrderSignature] using measurableSet_lt (htime a) (htime b)

/-- Finite truth table of the strict pairwise comparisons between mixed two-point events. -/
abbrev TwoPointOrderSignature (n : ℕ) :=
  Finset (TwoPointTimedEvent n × TwoPointTimedEvent n)

/-- The finite set of strict mixed-event comparisons true at one interaction-time assignment. -/
noncomputable def twoPointOrderSignature {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    TwoPointOrderSignature n :=
  strictOrderSignature (fun σ event => twoPointTimedEventTime τ τ' σ event) σ

/-- Two interaction-time assignments lie in the same mixed-order chamber exactly when
they determine the same finite strict-comparison signature. -/
theorem sameTwoPointOrderChamber_iff_orderSignature_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ' σ υ ↔
      twoPointOrderSignature τ τ' σ = twoPointOrderSignature τ τ' υ := by
  exact (strictOrderSignature_eq_iff
    (fun σ event => twoPointTimedEventTime τ τ' σ event) σ υ).symm

private theorem measurable_twoPointOrderSignature {n : ℕ} (τ τ' : ℝ) :
    Measurable (twoPointOrderSignature τ τ' :
      (Fin n → ℝ) → TwoPointOrderSignature n) := by
  exact measurable_strictOrderSignature
    (fun σ event => twoPointTimedEventTime τ τ' σ event)
    (fun event => (continuous_sumEventTime (twoPointExternalTimes τ τ') event).measurable)

/-- Fiber of the finite mixed-order signature map over a prescribed signature. -/
def twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) : Set (Fin n → ℝ) :=
  {σ | twoPointOrderSignature τ τ' σ = s}

theorem measurableSet_twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) :
    MeasurableSet (twoPointOrderSignatureFiber τ τ' s) := by
  classical
  change MeasurableSet
    (twoPointOrderSignature τ τ' ⁻¹' ({s} : Set (TwoPointOrderSignature n)))
  exact measurable_twoPointOrderSignature (n := n) τ τ' (MeasurableSet.singleton s)

/-!
## Arbitrary even external insertions

The `2 * E` external events and `n` interaction events are distinguished by a finite
strict-comparison signature. Its fibers form a measurable partition of the interaction-time
space, including all equal-time boundaries. This is the combinatorial input for analytic
regularity of arbitrary-external Dyson amplitudes.
-/

/-- Finite truth table of strict comparisons between arbitrary external and interaction events. -/
abbrev ExternalInsertionOrderSignature (E n : ℕ) :=
  Finset (ExternalInsertionTimedEvent E n × ExternalInsertionTimedEvent E n)

/-- All strict comparisons true at a given interaction-time assignment. -/
noncomputable def externalInsertionOrderSignature {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ExternalInsertionOrderSignature E n :=
  strictOrderSignature
    (fun σ event => externalInsertionTimedEventTime externalTime σ event) σ

/-- Two interaction-time assignments have identical strict event-time comparisons. -/
def SameExternalInsertionOrderChamber {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ) : Prop :=
  ∀ a b : ExternalInsertionTimedEvent E n,
    (externalInsertionTimedEventTime externalTime σ a <
      externalInsertionTimedEventTime externalTime σ b) ↔
    (externalInsertionTimedEventTime externalTime υ a <
      externalInsertionTimedEventTime externalTime υ b)

/-- The finite comparison signature identifies arbitrary-external order chambers. -/
theorem sameExternalInsertionOrderChamber_iff_orderSignature_eq {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ) :
    SameExternalInsertionOrderChamber externalTime σ υ ↔
      externalInsertionOrderSignature externalTime σ =
        externalInsertionOrderSignature externalTime υ := by
  exact (strictOrderSignature_eq_iff
    (fun σ event => externalInsertionTimedEventTime externalTime σ event) σ υ).symm

private theorem measurable_externalInsertionOrderSignature {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) :
    Measurable (externalInsertionOrderSignature externalTime :
      (Fin n → ℝ) → ExternalInsertionOrderSignature E n) := by
  exact measurable_strictOrderSignature
    (fun σ event => externalInsertionTimedEventTime externalTime σ event)
    (fun event => (continuous_sumEventTime externalTime event).measurable)

/-- The standard-to-mixed atomic-position permutation depends only on the finite
external-insertion order signature, including equal-time rank tie breaking. -/
theorem externalInsertionStandardToMixedAtomicPositionEquiv_eq_of_orderSignature_eq
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ)
    (h : externalInsertionOrderSignature externalTime σ =
      externalInsertionOrderSignature externalTime υ) :
    externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ =
      externalInsertionStandardToMixedAtomicPositionEquiv externalTime υ := by
  have horder :=
    externalInsertionMixedTimeOrderedAtomicLegEquiv_eq_of_comparisons
      externalTime σ υ
      ((sameExternalInsertionOrderChamber_iff_orderSignature_eq
        externalTime σ υ).2 h)
  unfold externalInsertionStandardToMixedAtomicPositionEquiv
  rw [horder]

/-- The interaction-time assignments realizing a fixed arbitrary-external order signature. -/
def externalInsertionOrderSignatureFiber {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ)
    (signature : ExternalInsertionOrderSignature E n) : Set (Fin n → ℝ) :=
  {σ | externalInsertionOrderSignature externalTime σ = signature}

/-- Every arbitrary-external mixed-order chamber is Borel measurable. -/
theorem measurableSet_externalInsertionOrderSignatureFiber {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ)
    (signature : ExternalInsertionOrderSignature E n) :
    MeasurableSet (externalInsertionOrderSignatureFiber externalTime signature) := by
  classical
  change MeasurableSet
    (externalInsertionOrderSignature externalTime ⁻¹'
      ({signature} : Set (ExternalInsertionOrderSignature E n)))
  exact measurable_externalInsertionOrderSignature externalTime
    (MeasurableSet.singleton signature)

end Common
end SecondQuantization

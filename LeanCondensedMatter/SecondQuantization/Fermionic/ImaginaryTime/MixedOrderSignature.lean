import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderWallMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option linter.style.header false

/-!
# Finite signatures for mixed two-point order chambers

A mixed-order chamber is completely determined by the truth values of the finitely many strict
comparisons between external and interaction events.  We package those true comparisons as a finite
set.  Equality of signatures is exactly `SameTwoPointOrderChamber`.

The fibers of the signature map are Borel measurable: each fiber is a finite/countable intersection
of strict-comparison sets or their complements.  This finite measurable partition is the interface
used to assemble globally measurable component factors from the continuous chamber representatives.
-/

namespace SecondQuantization
namespace Fermionic

/-- Finite truth table of all strict mixed-event comparisons. -/
abbrev TwoPointOrderSignature (n : ℕ) :=
  Finset (TwoPointTimedEvent n × TwoPointTimedEvent n)

/-- The strict mixed-event comparisons that hold for one interaction-time assignment. -/
def twoPointOrderSignature {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    TwoPointOrderSignature n :=
  Finset.univ.filter fun p =>
    twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2

@[simp]
theorem mem_twoPointOrderSignature_iff {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) :
    (a, b) ∈ twoPointOrderSignature τ τ' σ ↔
      twoPointTimedEventTime τ τ' σ a < twoPointTimedEventTime τ τ' σ b := by
  simp [twoPointOrderSignature]

/-- Equality of finite order signatures is exactly equality of mixed-order chambers. -/
theorem sameTwoPointOrderChamber_iff_orderSignature_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ' σ υ ↔
      twoPointOrderSignature τ τ' σ = twoPointOrderSignature τ τ' υ := by
  constructor
  · intro h
    ext p
    simpa only [mem_twoPointOrderSignature_iff] using h p.1 p.2
  · intro h a b
    have hp := Finset.ext_iff.mp h (a, b)
    simpa only [mem_twoPointOrderSignature_iff] using hp

/-- The strict-comparison locus of two fixed mixed events. -/
def twoPointEventStrictComparisonSet {n : ℕ} (τ τ' : ℝ)
    (a b : TwoPointTimedEvent n) : Set (Fin n → ℝ) :=
  {σ | twoPointTimedEventTime τ τ' σ a < twoPointTimedEventTime τ τ' σ b}

/-- The time of one fixed mixed event is continuous in the ambient interaction-time assignment. -/
theorem continuous_twoPointTimedEventTime {n : ℕ} (τ τ' : ℝ)
    (a : TwoPointTimedEvent n) :
    Continuous (fun σ : Fin n → ℝ => twoPointTimedEventTime τ τ' σ a) := by
  cases a with
  | inl e =>
      change Continuous (fun _ : Fin n → ℝ => twoPointExternalTimes τ τ' e)
      exact continuous_const
  | inr v =>
      change Continuous (fun σ : Fin n → ℝ => σ v)
      exact continuous_apply v

/-- Every strict mixed-event comparison locus is Borel measurable. -/
theorem measurableSet_twoPointEventStrictComparisonSet {n : ℕ} (τ τ' : ℝ)
    (a b : TwoPointTimedEvent n) :
    MeasurableSet (twoPointEventStrictComparisonSet τ τ' a b) := by
  exact measurableSet_lt
    (continuous_twoPointTimedEventTime τ τ' a).measurable
    (continuous_twoPointTimedEventTime τ τ' b).measurable

/-- Fiber of one finite mixed-order signature. -/
def twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) : Set (Fin n → ℝ) :=
  {σ | twoPointOrderSignature τ τ' σ = s}

private theorem twoPointOrderSignatureFiber_eq_iInter {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) :
    twoPointOrderSignatureFiber τ τ' s =
      ⋂ p : TwoPointTimedEvent n × TwoPointTimedEvent n,
        if p ∈ s then twoPointEventStrictComparisonSet τ τ' p.1 p.2
        else (twoPointEventStrictComparisonSet τ τ' p.1 p.2)ᶜ := by
  ext σ
  simp only [twoPointOrderSignatureFiber, Set.mem_setOf_eq, Set.mem_iInter,
    Set.mem_ite_iff, Set.mem_compl_iff, twoPointEventStrictComparisonSet, Set.mem_setOf_eq]
  constructor
  · intro h p
    have hp := Finset.ext_iff.mp h p
    by_cases hps : p ∈ s
    · left
      refine ⟨hps, ?_⟩
      simpa only [mem_twoPointOrderSignature_iff] using hp.mpr hps
    · right
      refine ⟨hps, ?_⟩
      intro hlt
      have : p ∈ twoPointOrderSignature τ τ' σ := by
        simpa only [mem_twoPointOrderSignature_iff] using hlt
      exact hps (hp.mp this)
  · intro h
    apply Finset.ext
    intro p
    have hp := h p
    by_cases hps : p ∈ s
    · have hlt :
          twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2 := by
        simpa [hps, twoPointEventStrictComparisonSet] using hp
      simpa only [mem_twoPointOrderSignature_iff, hps] using hlt
    · have hnlt :
          ¬ twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2 := by
        simpa [hps, twoPointEventStrictComparisonSet] using hp
      simp only [mem_twoPointOrderSignature_iff, hps, iff_false]
      exact hnlt

/-- Every finite mixed-order signature fiber is Borel measurable. -/
theorem measurableSet_twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) :
    MeasurableSet (twoPointOrderSignatureFiber τ τ' s) := by
  rw [twoPointOrderSignatureFiber_eq_iInter]
  apply MeasurableSet.iInter
  intro p
  by_cases hps : p ∈ s
  · simpa [hps] using measurableSet_twoPointEventStrictComparisonSet τ τ' p.1 p.2
  · simpa [hps] using
      (measurableSet_twoPointEventStrictComparisonSet τ τ' p.1 p.2).compl

/-- A chosen ambient assignment realizing a signature, falling back to the zero assignment for an
unrealized signature. -/
noncomputable def twoPointOrderSignatureBase {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) : Fin n → ℝ :=
  if h : ∃ σ : Fin n → ℝ, twoPointOrderSignature τ τ' σ = s then
    Classical.choose h
  else
    0

/-- The chosen base realizes every realized signature. -/
theorem twoPointOrderSignature_twoPointOrderSignatureBase_eq {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n)
    (h : ∃ σ : Fin n → ℝ, twoPointOrderSignature τ τ' σ = s) :
    twoPointOrderSignature τ τ' (twoPointOrderSignatureBase τ τ' s) = s := by
  rw [twoPointOrderSignatureBase, dif_pos h]
  exact Classical.choose_spec h

/-- Every assignment lies in the same order chamber as the chosen base of its own signature. -/
theorem sameTwoPointOrderChamber_signatureBase {n : ℕ} (τ τ' : ℝ)
    (σ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ'
      (twoPointOrderSignatureBase τ τ' (twoPointOrderSignature τ τ' σ)) σ := by
  rw [sameTwoPointOrderChamber_iff_orderSignature_eq]
  exact twoPointOrderSignature_twoPointOrderSignatureBase_eq τ τ'
    (twoPointOrderSignature τ τ' σ) ⟨σ, rfl⟩

end Fermionic
end SecondQuantization

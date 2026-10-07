import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option linter.style.header false

/-!
# Finite signatures for mixed two-point order chambers

A mixed-order chamber is completely determined by the truth values of the finitely many strict
comparisons between external and interaction events. The fibers of the signature map are Borel
measurable. This finite measurable partition depends only on the mixed event order, not statistics.
-/

namespace SecondQuantization
namespace Common

/-- Finite truth table of the strict pairwise comparisons between mixed two-point events. -/
abbrev TwoPointOrderSignature (n : ℕ) :=
  Finset (TwoPointTimedEvent n × TwoPointTimedEvent n)

/-- The finite set of strict mixed-event comparisons true at one interaction-time assignment. -/
noncomputable def twoPointOrderSignature {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    TwoPointOrderSignature n :=
  Finset.univ.filter fun p =>
    twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2

/-- Two interaction-time assignments lie in the same mixed-order chamber exactly when
they determine the same finite strict-comparison signature. -/
theorem sameTwoPointOrderChamber_iff_orderSignature_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ' σ υ ↔
      twoPointOrderSignature τ τ' σ = twoPointOrderSignature τ τ' υ := by
  classical
  constructor
  · intro h
    ext p
    rcases p with ⟨a, b⟩
    simpa [twoPointOrderSignature] using h a b
  · intro h a b
    have hp :
        ((a, b) ∈ twoPointOrderSignature τ τ' σ) ↔
          ((a, b) ∈ twoPointOrderSignature τ τ' υ) := by
      rw [h]
    simpa [twoPointOrderSignature] using hp

private theorem continuous_twoPointTimedEventTime {n : ℕ} (τ τ' : ℝ)
    (a : TwoPointTimedEvent n) :
    Continuous (fun σ : Fin n → ℝ => twoPointTimedEventTime τ τ' σ a) := by
  cases a with
  | inl e =>
      change Continuous (fun _ : Fin n → ℝ => twoPointExternalTimes τ τ' e)
      exact continuous_const
  | inr v =>
      change Continuous (fun σ : Fin n → ℝ => σ v)
      exact continuous_apply v

private theorem measurable_twoPointOrderSignature {n : ℕ} (τ τ' : ℝ) :
    Measurable (twoPointOrderSignature τ τ' :
      (Fin n → ℝ) → TwoPointOrderSignature n) := by
  rw [measurable_finset_iff_measurable_set, measurable_set_iff]
  rintro ⟨a, b⟩
  apply measurable_to_prop
  simpa [twoPointOrderSignature] using
    (measurableSet_lt
      (continuous_twoPointTimedEventTime τ τ' a).measurable
      (continuous_twoPointTimedEventTime τ τ' b).measurable)

/-- Fiber of the finite mixed-order signature map over a prescribed signature. -/
def twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) : Set (Fin n → ℝ) :=
  {σ | twoPointOrderSignature τ τ' σ = s}

theorem measurableSet_twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) :
    MeasurableSet (twoPointOrderSignatureFiber τ τ' s) := by
  classical
  have h := measurable_twoPointOrderSignature (n := n) τ τ' (MeasurableSet.singleton s)
  simpa [twoPointOrderSignatureFiber] using h

end Common
end SecondQuantization

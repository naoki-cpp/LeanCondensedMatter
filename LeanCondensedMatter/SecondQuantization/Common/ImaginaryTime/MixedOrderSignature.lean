import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderWallMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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

@[simp]
theorem mem_twoPointOrderSignature_iff {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) :
    (a, b) ∈ twoPointOrderSignature τ τ' σ ↔
      twoPointTimedEventTime τ τ' σ a < twoPointTimedEventTime τ τ' σ b := by
  classical
  simp [twoPointOrderSignature]

theorem sameTwoPointOrderChamber_iff_orderSignature_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ' σ υ ↔
      twoPointOrderSignature τ τ' σ = twoPointOrderSignature τ τ' υ := by
  classical
  constructor
  · intro h
    ext p
    rcases p with ⟨a, b⟩
    simpa only [mem_twoPointOrderSignature_iff] using h a b
  · intro h a b
    constructor
    · intro hab
      have hm : (a, b) ∈ twoPointOrderSignature τ τ' σ :=
        (mem_twoPointOrderSignature_iff τ τ' σ a b).2 hab
      rw [h] at hm
      exact (mem_twoPointOrderSignature_iff τ τ' υ a b).1 hm
    · intro hab
      have hm : (a, b) ∈ twoPointOrderSignature τ τ' υ :=
        (mem_twoPointOrderSignature_iff τ τ' υ a b).2 hab
      rw [← h] at hm
      exact (mem_twoPointOrderSignature_iff τ τ' σ a b).1 hm

/-- Locus of interaction-time assignments for which one fixed mixed event is strictly earlier than
another in physical time. -/
def twoPointEventStrictComparisonSet {n : ℕ} (τ τ' : ℝ)
    (a b : TwoPointTimedEvent n) : Set (Fin n → ℝ) :=
  {σ | twoPointTimedEventTime τ τ' σ a < twoPointTimedEventTime τ τ' σ b}

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

theorem measurableSet_twoPointEventStrictComparisonSet {n : ℕ} (τ τ' : ℝ)
    (a b : TwoPointTimedEvent n) :
    MeasurableSet (twoPointEventStrictComparisonSet τ τ' a b) := by
  exact measurableSet_lt
    (continuous_twoPointTimedEventTime τ τ' a).measurable
    (continuous_twoPointTimedEventTime τ τ' b).measurable

/-- Fiber of the finite mixed-order signature map over a prescribed signature. -/
def twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) : Set (Fin n → ℝ) :=
  {σ | twoPointOrderSignature τ τ' σ = s}

private theorem twoPointOrderSignatureFiber_eq_iInter {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) :
    twoPointOrderSignatureFiber τ τ' s =
      ⋂ p : TwoPointTimedEvent n × TwoPointTimedEvent n,
        if p ∈ s then twoPointEventStrictComparisonSet τ τ' p.1 p.2
        else (twoPointEventStrictComparisonSet τ τ' p.1 p.2)ᶜ := by
  classical
  ext σ
  simp only [twoPointOrderSignatureFiber, Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h p
    have hp : p ∈ twoPointOrderSignature τ τ' σ ↔ p ∈ s := by
      rw [h]
    by_cases hps : p ∈ s
    · have hmem : p ∈ twoPointOrderSignature τ τ' σ := hp.mpr hps
      have hlt :
          twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2 := by
        rcases p with ⟨a, b⟩
        simpa only [mem_twoPointOrderSignature_iff] using hmem
      simpa [hps, twoPointEventStrictComparisonSet] using hlt
    · have hnot : p ∉ twoPointOrderSignature τ τ' σ := by
        intro hmem
        exact hps (hp.mp hmem)
      have hnlt :
          ¬ twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2 := by
        rcases p with ⟨a, b⟩
        simpa only [mem_twoPointOrderSignature_iff] using hnot
      simpa [hps, twoPointEventStrictComparisonSet] using hnlt
  · intro h
    apply Finset.ext
    intro p
    have hp := h p
    by_cases hps : p ∈ s
    · have hlt :
          twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2 := by
        simpa [hps, twoPointEventStrictComparisonSet] using hp
      have hmem : p ∈ twoPointOrderSignature τ τ' σ := by
        rcases p with ⟨a, b⟩
        simpa only [mem_twoPointOrderSignature_iff] using hlt
      exact iff_of_true hmem hps
    · have hnlt :
          ¬ twoPointTimedEventTime τ τ' σ p.1 < twoPointTimedEventTime τ τ' σ p.2 := by
        simpa [hps, twoPointEventStrictComparisonSet] using hp
      have hnot : p ∉ twoPointOrderSignature τ τ' σ := by
        rcases p with ⟨a, b⟩
        simpa only [mem_twoPointOrderSignature_iff] using hnlt
      exact iff_of_false hnot hps

theorem measurableSet_twoPointOrderSignatureFiber {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) :
    MeasurableSet (twoPointOrderSignatureFiber τ τ' s) := by
  classical
  rw [twoPointOrderSignatureFiber_eq_iInter]
  apply MeasurableSet.iInter
  intro p
  by_cases hps : p ∈ s
  · simpa [hps] using measurableSet_twoPointEventStrictComparisonSet τ τ' p.1 p.2
  · simpa [hps] using
      (measurableSet_twoPointEventStrictComparisonSet τ τ' p.1 p.2).compl

/-- Chosen interaction-time assignment realizing a signature when it is realizable, with the zero
assignment as a fallback for unrealized signatures. -/
noncomputable def twoPointOrderSignatureBase {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n) : Fin n → ℝ := by
  classical
  exact if h : ∃ σ : Fin n → ℝ, twoPointOrderSignature τ τ' σ = s then
    Classical.choose h
  else
    0

theorem twoPointOrderSignature_twoPointOrderSignatureBase_eq {n : ℕ} (τ τ' : ℝ)
    (s : TwoPointOrderSignature n)
    (h : ∃ σ : Fin n → ℝ, twoPointOrderSignature τ τ' σ = s) :
    twoPointOrderSignature τ τ' (twoPointOrderSignatureBase τ τ' s) = s := by
  classical
  simp only [twoPointOrderSignatureBase, dif_pos h]
  exact Classical.choose_spec h

theorem sameTwoPointOrderChamber_signatureBase {n : ℕ} (τ τ' : ℝ)
    (σ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ'
      (twoPointOrderSignatureBase τ τ' (twoPointOrderSignature τ τ' σ)) σ := by
  rw [sameTwoPointOrderChamber_iff_orderSignature_eq]
  exact twoPointOrderSignature_twoPointOrderSignatureBase_eq τ τ'
    (twoPointOrderSignature τ τ' σ) ⟨σ, rfl⟩

end Common
end SecondQuantization

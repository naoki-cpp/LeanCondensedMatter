import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointFrequencyDomain
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option linter.style.header false

/-!
# Explicit ordering of response limits

This module keeps three logically different operations separate:

1. the observation-time limit `T → ∞` at fixed frequency and fixed positive switching rate;
2. removal of the adiabatic regulator `η → 0⁺` at fixed frequency;
3. the static limit `ω → 0`.

The finite-time transform is proved to converge to the fixed-positive-rate susceptibility.  The two
remaining limits are represented by different named predicates, including both possible iterated
orders.  No theorem identifies those orders, and no `η → 0⁺` or `ω → 0` limit is asserted without
an explicit convergence hypothesis.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- The switched response observed only over the finite causal window `(0,T]`. -/
noncomputable def finiteTimeAdiabaticFrequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta T : ℝ) : ℂ :=
  ∫ τ : ℝ in Ioc 0 T,
    adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ

/-- The same fixed-rate transform written directly as an integral over the open causal half-line. -/
noncomputable def causalAdiabaticFrequencyDomainSusceptibility
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  ∫ τ : ℝ in Ioi 0,
    adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ

/-- Causality reduces the full-real-line fixed-rate transform to the positive half-line.  The value
at `τ = 0` is retained by first restricting to `Ici 0`; `Ici` and `Ioi` have the same Lebesgue
integral because a singleton has zero measure. -/
theorem adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eq_causal
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        expectation A B omega eta hη =
      causalAdiabaticFrequencyDomainSusceptibility system
        expectation A B omega eta := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate,
    adiabaticFrequencyDomainSusceptibility,
    causalAdiabaticFrequencyDomainSusceptibility]
  calc
    (∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ) =
      ∫ τ : ℝ,
        (Ici (0 : ℝ)).indicator
          (adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta) τ := by
      apply integral_congr_ae
      filter_upwards [] with τ
      by_cases hτ : τ ∈ Ici (0 : ℝ)
      · simp [hτ]
      · have hneg : τ < 0 := by simpa [Set.mem_Ici, not_le] using hτ
        have hzero := adiabaticFrequencySusceptibilityIntegrand_eq_zero_of_neg
          system expectation A B omega eta hneg
        simp [hτ, hzero]
    _ = ∫ τ : ℝ in Ici 0,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ :=
      integral_indicator measurableSet_Ici
    _ = ∫ τ : ℝ in Ioi 0,
        adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta τ :=
      integral_Ici_eq_integral_Ioi

/-- At fixed frequency and fixed positive switching rate, increasing the observation window to
infinity converges to the causal fixed-rate transform. -/
theorem tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    Tendsto
      (fun T : ℝ =>
        finiteTimeAdiabaticFrequencyDomainSusceptibility system
          expectation A B omega eta T)
      atTop
      (𝓝 (causalAdiabaticFrequencyDomainSusceptibility system
        expectation A B omega eta)) := by
  let f : ℝ → ℂ :=
    adiabaticFrequencySusceptibilityIntegrand system expectation A B omega eta
  have hInt : Integrable f :=
    (adiabaticIntegrable_of_pos system expectation A B omega eta hη).integrable
  have hunion : (⋃ T : ℝ, Ioc (0 : ℝ) T) = Ioi 0 := by
    ext τ
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨T, hpos, _⟩
      exact hpos
    · intro hpos
      exact ⟨τ, hpos, le_rfl⟩
  have ht := tendsto_setIntegral_of_monotone
    (f := f) (μ := volume)
    (s := fun T : ℝ => Ioc 0 T)
    (fun _ => measurableSet_Ioc)
    (fun _ _ hab _ hx => ⟨hx.1, hx.2.trans hab⟩)
    (by
      rw [hunion]
      exact hInt.integrableOn)
  rw [hunion] at ht
  simpa [finiteTimeAdiabaticFrequencyDomainSusceptibility,
    causalAdiabaticFrequencyDomainSusceptibility, f] using ht

/-- The physical fixed-rate susceptibility is therefore obtained by taking `T → ∞` first, while
`omega` and the positive rate `eta` remain fixed. -/
theorem tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop_eq_fixedRate
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) (omega eta : ℝ) (hη : 0 < eta) :
    Tendsto
      (fun T : ℝ =>
        finiteTimeAdiabaticFrequencyDomainSusceptibility system
          expectation A B omega eta T)
      atTop
      (𝓝 (adiabaticFrequencyDomainSusceptibilityOfPositiveRate system
        expectation A B omega eta hη)) := by
  rw [adiabaticFrequencyDomainSusceptibilityOfPositiveRate_eq_causal
    system expectation A B omega eta hη]
  exact tendsto_finiteTimeAdiabaticFrequencyDomainSusceptibility_atTop
    system expectation A B omega eta hη

/-- Removal of a positive regulator: `eta → 0⁺`. -/
def HasAdiabaticRemovalLimit (f : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto f (nhdsWithin 0 (Ioi 0)) (𝓝 L)

/-- Static limit: `omega → 0` through an ordinary two-sided neighborhood. -/
def HasStaticLimit (f : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto f (𝓝 0) (𝓝 L)

/-- Finite sums preserve regulator-removal limits term by term. -/
theorem HasAdiabaticRemovalLimit.finsetSum {κ : Type*} (s : Finset κ)
    (f : κ → ℝ → ℂ) (L : κ → ℂ)
    (h : ∀ j ∈ s, HasAdiabaticRemovalLimit (f j) (L j)) :
    HasAdiabaticRemovalLimit
      (fun eta => s.sum fun j => f j eta)
      (s.sum L) := by
  unfold HasAdiabaticRemovalLimit
  exact tendsto_finsetSum s fun j hj => h j hj

/-- Finite sums preserve static limits term by term. -/
theorem HasStaticLimit.finsetSum {κ : Type*} (s : Finset κ)
    (f : κ → ℝ → ℂ) (L : κ → ℂ)
    (h : ∀ j ∈ s, HasStaticLimit (f j) (L j)) :
    HasStaticLimit
      (fun omega => s.sum fun j => f j omega)
      (s.sum L) := by
  unfold HasStaticLimit
  exact tendsto_finsetSum s fun j hj => h j hj

/-- First take the static limit at every fixed positive rate, then remove the regulator. -/
def HasStaticThenAdiabaticLimit
    (F : ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ staticAtRate : ℝ → ℂ,
    (∀ eta, 0 < eta → HasStaticLimit (fun omega => F omega eta) (staticAtRate eta)) ∧
    HasAdiabaticRemovalLimit staticAtRate L

/-- First remove the regulator at every fixed frequency, then take the static limit. -/
def HasAdiabaticThenStaticLimit
    (F : ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ regulatorRemoved : ℝ → ℂ,
    (∀ omega, HasAdiabaticRemovalLimit (fun eta => F omega eta) (regulatorRemoved omega)) ∧
    HasStaticLimit regulatorRemoved L

/-- Explicit order `T → ∞`, then `omega → 0`, then `eta → 0⁺`. -/
def HasLongTimeThenStaticThenAdiabaticLimit
    (F : ℝ → ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ fixedRate : ℝ → ℝ → ℂ,
    (∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta))) ∧
    HasStaticThenAdiabaticLimit fixedRate L

/-- Explicit order `T → ∞`, then `eta → 0⁺`, then `omega → 0`. -/
def HasLongTimeThenAdiabaticThenStaticLimit
    (F : ℝ → ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ fixedRate : ℝ → ℝ → ℂ,
    (∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta))) ∧
    HasAdiabaticThenStaticLimit fixedRate L

/-- The two orders are intentionally separate propositions; providing one does not silently provide
the other.  This constructor records the long-time theorem together with an independently proved
static-then-adiabatic limit. -/
theorem hasLongTimeThenStaticThenAdiabaticLimit_of_components
    {F : ℝ → ℝ → ℝ → ℂ} {fixedRate : ℝ → ℝ → ℂ} {L : ℂ}
    (hT : ∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta)))
    (hlimits : HasStaticThenAdiabaticLimit fixedRate L) :
    HasLongTimeThenStaticThenAdiabaticLimit F L :=
  ⟨fixedRate, hT, hlimits⟩

/-- Analogous constructor for the adiabatic-then-static order. -/
theorem hasLongTimeThenAdiabaticThenStaticLimit_of_components
    {F : ℝ → ℝ → ℝ → ℂ} {fixedRate : ℝ → ℝ → ℂ} {L : ℂ}
    (hT : ∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta)))
    (hlimits : HasAdiabaticThenStaticLimit fixedRate L) :
    HasLongTimeThenAdiabaticThenStaticLimit F L :=
  ⟨fixedRate, hT, hlimits⟩

end
end LinearResponse
end QuantumTheory
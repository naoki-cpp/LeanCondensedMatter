import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option linter.style.header false

/-! # Order of scalar response limits -/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory Filter Topology

noncomputable section

/-- Existence of the observation-time limit `T → +∞` at fixed values of all other parameters. -/
def HasInfiniteObservationTimeLimit
    (response : ℝ → ℂ) (value : ℂ) : Prop :=
  Filter.Tendsto response Filter.atTop (nhds value)

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

/-- Local static-then-adiabatic order. -/
def HasLocalStaticThenAdiabaticLimit
    (F : ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ staticAtRate : ℝ → ℂ,
    (∀ᶠ eta in nhdsWithin 0 (Ioi 0),
      HasStaticLimit (fun omega => F omega eta) (staticAtRate eta)) ∧
    HasAdiabaticRemovalLimit staticAtRate L

/-- Local adiabatic-then-static order. -/
def HasLocalAdiabaticThenStaticLimit
    (F : ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ regulatorRemoved : ℝ → ℂ,
    (∀ᶠ omega in 𝓝 0,
      HasAdiabaticRemovalLimit (fun eta => F omega eta) (regulatorRemoved omega)) ∧
    HasStaticLimit regulatorRemoved L

/-- Long time first, followed by the local static-then-adiabatic order. -/
def HasLongTimeThenLocalStaticThenAdiabaticLimit
    (F : ℝ → ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ fixedRate : ℝ → ℝ → ℂ,
    (∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta))) ∧
    HasLocalStaticThenAdiabaticLimit fixedRate L

/-- Long time first, followed by the local adiabatic-then-static order. -/
def HasLongTimeThenLocalAdiabaticThenStaticLimit
    (F : ℝ → ℝ → ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ fixedRate : ℝ → ℝ → ℂ,
    (∀ omega eta, 0 < eta →
      Tendsto (fun T => F T omega eta) atTop (𝓝 (fixedRate omega eta))) ∧
    HasLocalAdiabaticThenStaticLimit fixedRate L

end
end LinearResponse
end QuantumTheory

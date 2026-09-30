import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.Combinatorics.Cumulant.NormalizedCore

set_option linter.style.header false

/-!
# Factorial-normalized power-series moments

This module packages factorial-normalized power-series coefficients as finite-set moment data.
It is deliberately independent of cumulant inversion so both replica and Möbius-inversion proof
tracks can share the same moment interface.
-/

namespace Combinatorics

open PowerSeries

/-- The exponential-generating-function normalization of a power-series coefficient. -/
noncomputable def powerSeriesMomentCoeff (Z : PowerSeries ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n Z

/-- Factorial-normalized coefficients of a unit-constant power series, bundled as normalized
finite-set moment data. -/
noncomputable def powerSeriesMomentSetFunction
    {α : Type*} (Z : PowerSeries ℂ)
    (hZ : PowerSeries.constantCoeff Z = 1) :
    NormalizedSetFunction α ℂ where
  toFun := fun S => powerSeriesMomentCoeff Z S.card
  map_empty := by
    simp [powerSeriesMomentCoeff, PowerSeries.coeff_zero_eq_constantCoeff, hZ]

/-- Equality of the bundled power-series moment function with normalized finite-set moment data is
equivalent to equality of the factorial-normalized coefficients on every finite set. -/
theorem powerSeriesMomentSetFunction_eq_iff
    {α : Type*} (Z : PowerSeries ℂ)
    (hZ : PowerSeries.constantCoeff Z = 1)
    (M : NormalizedSetFunction α ℂ) :
    powerSeriesMomentSetFunction Z hZ = M ↔
      ∀ S : Finset α, powerSeriesMomentCoeff Z S.card = M S := by
  constructor
  · intro h S
    change powerSeriesMomentSetFunction (α := α) Z hZ S = M S
    rw [h]
  · intro h
    apply NormalizedSetFunction.ext
    intro S
    change powerSeriesMomentCoeff Z S.card = M S
    exact h S

end Combinatorics

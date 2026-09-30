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
noncomputable def powerSeriesMomentCoeff
    {R : Type*} [Semiring R] (Z : PowerSeries R) (n : ℕ) : R :=
  (n.factorial : R) * PowerSeries.coeff n Z

/-- Factorial-normalized coefficients of a unit-constant power series, bundled as normalized
finite-set moment data. -/
noncomputable def powerSeriesMomentSetFunction
    {α R : Type*} [Semiring R] (Z : PowerSeries R)
    (hZ : PowerSeries.constantCoeff Z = 1) :
    NormalizedSetFunction α R where
  toFun := fun S => powerSeriesMomentCoeff Z S.card
  map_empty := by
    simp [powerSeriesMomentCoeff, PowerSeries.coeff_zero_eq_constantCoeff, hZ]

/-- Equality of the bundled power-series moment function with normalized finite-set moment data is
equivalent to equality of the factorial-normalized coefficients on every finite set. -/
theorem powerSeriesMomentSetFunction_eq_iff
    {α R : Type*} [Semiring R] (Z : PowerSeries R)
    (hZ : PowerSeries.constantCoeff Z = 1)
    (M : NormalizedSetFunction α R) :
    powerSeriesMomentSetFunction Z hZ = M ↔
      ∀ S : Finset α, powerSeriesMomentCoeff Z S.card = M S := by
  constructor
  · rintro rfl S
    rfl
  · intro h
    exact NormalizedSetFunction.ext h

end Combinatorics

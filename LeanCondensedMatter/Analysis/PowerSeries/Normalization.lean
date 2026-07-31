import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Normalization of power series by their constant coefficient

This module contains the statistics-independent normalization used by perturbative partition
series.  For a power series with nonzero constant coefficient, multiplication by its inverse
produces a series with constant coefficient `1`.

The formal logarithm itself is not redefined here: Mathlib's `PowerSeries.logOf` is the
authoritative construction for `log(1 + (Z - 1))`.
-/

namespace PowerSeries

variable {R : Type*} [Field R]

/-- Normalize a power series by multiplying it by the inverse of its constant coefficient. -/
noncomputable def normalizeByConstantCoeff (Z : PowerSeries R) : PowerSeries R :=
  C (constantCoeff Z)⁻¹ * Z

/-- A power series normalized by a nonzero constant coefficient has constant coefficient `1`. -/
theorem constantCoeff_normalizeByConstantCoeff {Z : PowerSeries R}
    (hZ : constantCoeff Z ≠ 0) :
    constantCoeff (normalizeByConstantCoeff Z) = 1 := by
  rw [normalizeByConstantCoeff, map_mul, constantCoeff_C, inv_mul_cancel₀ hZ]

end PowerSeries

import Mathlib.Data.Int.Basic

set_option linter.style.header false

/-!
# Quantum statistics: bosons and fermions

The two exchange statistics available to identical particles, and the sign `ζ ∈ {+1, -1}` that
distinguishes their (anti)commutation relations — `+1` for bosons (CCR), `-1` for fermions (CAR).
Kept as its own tiny file so both occupation-number representations
(`BosonOccupation.lean`, `FermionOccupation.lean`) and, later, a unified statement of CCR/CAR can
refer to it without duplicating the sign convention.
-/

namespace SecondQuantization

/-- **Quantum statistics.** Which of the two exchange statistics a species of identical particle
obeys. -/
inductive Statistics
  | boson
  | fermion
  deriving DecidableEq, Repr

namespace Statistics

/-- **The exchange sign** `ζ`: `+1` for bosons, `-1` for fermions. This is the sign that appears
in the (anti)commutation relations `a_i a_j† - ζ a_j† a_i = δᵢⱼ` unifying CCR (`ζ = 1`) and CAR
(`ζ = -1`). -/
def zetaInt : Statistics → ℤ
  | boson => 1
  | fermion => -1

@[simp]
theorem zetaInt_boson : zetaInt boson = 1 := rfl

@[simp]
theorem zetaInt_fermion : zetaInt fermion = -1 := rfl

@[simp]
theorem zeta_sq (s : Statistics) : zetaInt s * zetaInt s = 1 := by
  cases s <;> decide

end Statistics

end SecondQuantization

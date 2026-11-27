import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Two-band spectral branches

The two branches of a spectrum of the form ε₀ ± E, their signs and interchange,
and the energy difference independent of the common scalar shift.
No Hamiltonian or momentum model is assumed.
-/

namespace QuantumTheory

/-- Lower and upper branches of a two-band spectrum. -/
inductive TwoBand where
  | lower
  | upper
  deriving DecidableEq

namespace TwoBand

instance : Fintype TwoBand where
  elems := {.lower, .upper}
  complete := by intro band; cases band <;> simp

/-- Sum over the two branches. -/
theorem sum_band {M : Type*} [AddCommMonoid M] (f : TwoBand → M) :
    ∑ band : TwoBand, f band = f .lower + f .upper := by
  change ∑ band ∈ ({.lower, .upper} : Finset TwoBand), f band = _
  simp

/-- Interchange the two spectral branches. -/
def oppositeBand : TwoBand → TwoBand
  | .lower => .upper
  | .upper => .lower

@[simp] theorem oppositeBand_lower : oppositeBand .lower = .upper := rfl
@[simp] theorem oppositeBand_upper : oppositeBand .upper = .lower := rfl
@[simp] theorem oppositeBand_oppositeBand (band : TwoBand) :
    oppositeBand (oppositeBand band) = band := by
  cases band <;> rfl

/-- Sign of the energy relative to the common scalar shift. -/
def bandSign : TwoBand → ℝ
  | .lower => -1
  | .upper => 1

@[simp] theorem bandSign_lower : bandSign .lower = -1 := rfl
@[simp] theorem bandSign_upper : bandSign .upper = 1 := rfl

@[simp] theorem bandSign_oppositeBand (band : TwoBand) :
    bandSign (oppositeBand band) = -bandSign band := by
  cases band <;> simp [oppositeBand, bandSign]

@[simp] theorem bandSign_sq (band : TwoBand) : bandSign band ^ 2 = 1 := by
  cases band <;> simp [bandSign]

/-- The opposite branch is distinct. -/
theorem ne_oppositeBand (band : TwoBand) : band ≠ oppositeBand band := by
  cases band <;> decide

/-- A scalar-shifted signed energy has distinct branches away from degeneracy. -/
theorem shiftedEnergy_injective (ε E : ℝ) (hE : E ≠ 0) :
    Function.Injective (fun band : TwoBand => ε + bandSign band * E) := by
  intro a b hab
  cases a <;> cases b <;> try rfl
  all_goals exact (hE (by simp [bandSign] at hab; linarith)).elim

/-- The interband energy difference cancels the common scalar shift. -/
theorem shiftedEnergy_sub_oppositeBand (band : TwoBand) (ε E : ℝ) :
    (ε + bandSign band * E) -
        (ε + bandSign (oppositeBand band) * E) = 2 * bandSign band * E := by
  rw [bandSign_oppositeBand]
  ring

end TwoBand
end QuantumTheory

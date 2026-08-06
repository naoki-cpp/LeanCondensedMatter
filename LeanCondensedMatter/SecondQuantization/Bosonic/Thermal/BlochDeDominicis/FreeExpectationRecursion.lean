import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.NormalizedTwoPoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson convergence-aware Wick recursion

This module fixes the concrete free thermal field labels, ordered algebraic-Fock product, and
normalized pair kernel used by the bosonic Wick recursion.  The remaining analytic obligations are
kept explicit: admissibility must imply Gibbs summability, survive pair deletion, and satisfy the
first-pair KMS/exchange recurrence.
-/

namespace SecondQuantization
namespace Bosonic

open Common Combinatorics

noncomputable section

/-- A local free-boson thermal field: either an annihilator or a creator in one mode. -/
inductive FreeThermalField (Mode : Type*)
  | annihilate (mode : Mode)
  | create (mode : Mode)
  deriving DecidableEq

namespace FreeThermalField

variable {Mode : Type*}

/-- Algebraic-Fock realization of a free thermal field label. -/
def operator : FreeThermalField Mode → (FockSpace Mode →ₗ[ℂ] FockSpace Mode)
  | .annihilate i => Bosonic.annihilate i
  | .create i => Bosonic.create i

/-- Ordered composition of free thermal fields, with the leftmost list entry acting last. -/
def orderedProduct : List (FreeThermalField Mode) → (FockSpace Mode →ₗ[ℂ] FockSpace Mode)
  | [] => LinearMap.id
  | field :: fields => (operator field).comp (orderedProduct fields)

@[simp] theorem orderedProduct_nil : orderedProduct ([] : List (FreeThermalField Mode)) = LinearMap.id := rfl

end FreeThermalField

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- The canonical normalized free-boson pair kernel.

The `annihilate/create` entry is the two-point value proved in `NormalizedTwoPoint`.  The reverse
entry is its KMS-rotated Bose occupation value.  Equal-type entries vanish. -/
def freeThermalPairValue (ε : Mode → ℝ) (β : ℝ) :
    FreeThermalField Mode → FreeThermalField Mode → ℂ
  | .annihilate i, .create j =>
      if i = j then (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ))⁻¹ else 0
  | .create i, .annihilate j =>
      if i = j then Complex.exp ((-(ε j) * β : ℝ) : ℂ) *
        (1 - Complex.exp ((-(ε j) * β : ℝ) : ℂ))⁻¹ else 0
  | .annihilate _, .annihilate _ => 0
  | .create _, .create _ => 0

/-- Canonical constructor for the free-boson convergence-aware pairing recursion.

All genuinely analytic input remains in the three hypotheses: product summability, deletion closure,
and the KMS first-pair recurrence. -/
def freeGibbsPairingRecursion
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (admissible : (n : ℕ) → (Fin (2 * n) → FreeThermalField Mode) → Prop)
    (hmem : ∀ (n : ℕ) (C : Fin (2 * n) → FreeThermalField Mode), admissible n C →
      FreeThermalField.orderedProduct (List.ofFn C) ∈ freeGibbsDomain ε β)
    (herase : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → FreeThermalField Mode), admissible (n + 1) C →
      ∀ j : Fin (2 * n + 1),
        admissible n (fun i : Fin (2 * n) => C ((j.succAbove i).succ)))
    (hrec : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → FreeThermalField Mode), admissible (n + 1) C →
      (freeGibbsFunctional ε β hpos).value
          (FreeThermalField.orderedProduct (List.ofFn C)) =
        ∑ j : Fin (2 * n + 1),
          freeThermalPairValue ε β (C 0) (C j.succ) *
            (freeGibbsFunctional ε β hpos).value
              (FreeThermalField.orderedProduct
                (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ)))) :
    ConvergenceAwarePairingRecursion
      (FockSpace Mode →ₗ[ℂ] FockSpace Mode) (FreeThermalField Mode) .boson where
  functional := freeGibbsFunctional ε β hpos
  orderedProduct := FreeThermalField.orderedProduct
  pairValue := freeThermalPairValue ε β
  admissible := admissible
  orderedProduct_mem := hmem
  orderedProduct_nil := rfl
  admissible_erase := herase
  expectation_succ := by
    intro n C hC
    simpa using hrec n C hC

/-- The full free-boson Wick pairing expansion obtained from the Common induction. -/
theorem freeGibbsExpectation_eq_sum_pairing
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (admissible : (n : ℕ) → (Fin (2 * n) → FreeThermalField Mode) → Prop)
    (hmem : ∀ (n : ℕ) (C : Fin (2 * n) → FreeThermalField Mode), admissible n C →
      FreeThermalField.orderedProduct (List.ofFn C) ∈ freeGibbsDomain ε β)
    (herase : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → FreeThermalField Mode), admissible (n + 1) C →
      ∀ j : Fin (2 * n + 1),
        admissible n (fun i : Fin (2 * n) => C ((j.succAbove i).succ)))
    (hrec : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → FreeThermalField Mode), admissible (n + 1) C →
      (freeGibbsFunctional ε β hpos).value
          (FreeThermalField.orderedProduct (List.ofFn C)) =
        ∑ j : Fin (2 * n + 1),
          freeThermalPairValue ε β (C 0) (C j.succ) *
            (freeGibbsFunctional ε β hpos).value
              (FreeThermalField.orderedProduct
                (List.ofFn fun i : Fin (2 * n) => C ((j.succAbove i).succ))))
    (n : ℕ) (C : Fin (2 * n) → FreeThermalField Mode) (hC : admissible n C) :
    (freeGibbsFunctional ε β hpos).value
        (FreeThermalField.orderedProduct (List.ofFn C)) =
      ∑ pairing : Pairing n,
        pairing.weight .boson *
          ∏ pr ∈ pairing.pairs, freeThermalPairValue ε β (C pr.1) (C pr.2) := by
  let data := freeGibbsPairingRecursion ε β hpos admissible hmem herase hrec
  exact data.expectation_eq_sum_pairing n C hC

end
end Bosonic
end SecondQuantization

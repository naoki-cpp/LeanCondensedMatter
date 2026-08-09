import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.NormalizedTwoPoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson thermal field data

This module owns the concrete free thermal field labels, their ordered algebraic-Fock product, and
the normalized two-point kernel. Number-conserving multipoint Gibbs expectations are evaluated by
the permanent backend in `ConcreteExpectationRecursion`.

The previous free-boson perfect-pairing recursion constructor and pairing-sum endpoint are removed:
for the present free state, same-type contractions vanish and the surviving bipartite matchings are
permutations. General Gaussian bosonic pairing evaluation is reserved for the later Hafnian backend.
-/

namespace SecondQuantization
namespace Bosonic

open Common

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

The `annihilate/create` entry is the two-point value proved in `NormalizedTwoPoint`. The reverse
entry is its KMS-rotated Bose occupation value. Equal-type entries vanish. -/
def freeThermalPairValue (ε : Mode → ℝ) (β : ℝ) :
    FreeThermalField Mode → FreeThermalField Mode → ℂ
  | .annihilate i, .create j =>
      if i = j then (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ))⁻¹ else 0
  | .create i, .annihilate j =>
      if i = j then Complex.exp ((-(ε j) * β : ℝ) : ℂ) *
        (1 - Complex.exp ((-(ε j) * β : ℝ) : ℂ))⁻¹ else 0
  | .annihilate _, .annihilate _ => 0
  | .create _, .create _ => 0

end
end Bosonic
end SecondQuantization

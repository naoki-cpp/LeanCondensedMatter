import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Analysis.Complex.Exponential

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson thermal field data

Free thermal field labels, their ordered algebraic-Fock products, and the normalized free pair
kernel. The kernel's equality to Gibbs two-field expectations is proved in
`Thermal/BlochDeDominicis/ConcretePairKernel`. These data are independent of the pairing-recursion
construction and its convergence-aware Gibbs functional.
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
def orderedProduct (fields : List (FreeThermalField Mode)) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (fields.map operator).prod

@[simp] theorem orderedProduct_nil :
    orderedProduct ([] : List (FreeThermalField Mode)) = LinearMap.id := by
  simp [orderedProduct, Module.End.one_eq_id]

@[simp] theorem orderedProduct_cons (field : FreeThermalField Mode)
    (fields : List (FreeThermalField Mode)) :
    orderedProduct (field :: fields) =
      field.operator.comp (orderedProduct fields) := by
  simp [orderedProduct, Module.End.mul_eq_comp]

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

end
end Bosonic
end SecondQuantization

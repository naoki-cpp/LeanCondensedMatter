import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteMixedTwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeThermalField

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete realization of the free thermal pair kernel

The mixed creation-annihilation two-point functions are given by the corresponding convergent free
Gibbs expectations. Same-type pairs have identically zero diagonal coefficients, hence zero
Gibbs numerators and zero normalized expectations.

Together these cases identify `freeThermalPairValue` with the convergence-aware free Gibbs
expectation of every ordered two-field product.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality used by the concrete pair kernel. -/
local instance instDecidableEqConcretePairKernel : DecidableEq Mode := Classical.decEq Mode

variable [Fintype Mode]

/-- The canonical free thermal pair kernel is exactly the normalized free-Gibbs expectation of the
corresponding ordered two-field product. -/
theorem freeGibbsExpectation_orderedProduct_pair_eq_freeThermalPairValue
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k)
    (f g : FreeThermalField Mode) :
    freeGibbsExpectation ε β (FreeThermalField.orderedProduct [f, g]) =
      freeThermalPairValue ε β f g := by
  cases f with
  | annihilate i =>
      cases g with
      | annihilate j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            (freeGibbsExpectation_eq_zero_of_matrixCoeff_self_eq_zero ε β
              ((_root_.SecondQuantization.Bosonic.annihilate i).comp
                (_root_.SecondQuantization.Bosonic.annihilate j))
              (matrixCoeff_annihilate_comp_annihilate i j))
      | create j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            freeGibbsExpectation_annihilate_comp_create_concrete ε β hpos i j
  | create i =>
      cases g with
      | annihilate j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            freeGibbsExpectation_create_comp_annihilate_concrete ε β hpos i j
      | create j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            (freeGibbsExpectation_eq_zero_of_matrixCoeff_self_eq_zero ε β
              ((_root_.SecondQuantization.Bosonic.create i).comp
                (_root_.SecondQuantization.Bosonic.create j))
              (matrixCoeff_create_comp_create i j))

end
end Bosonic
end SecondQuantization

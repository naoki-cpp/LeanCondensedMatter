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

/-- The grand-canonical free thermal pair kernel is exactly the normalized free-Gibbs expectation of the
corresponding ordered two-field product. -/
theorem grandCanonicalGibbsExpectation_orderedProduct_pair_eq_freeThermalPairValue
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ k, 0 < β * (ε k - μ))
    (f g : FreeThermalField Mode) :
    grandCanonicalGibbsExpectation ε β μ (FreeThermalField.orderedProduct [f, g]) =
      freeThermalPairValue (fun i => ε i - μ) β f g := by
  cases f with
  | annihilate i =>
      cases g with
      | annihilate j =>
          have hzero : grandCanonicalGibbsExpectation ε β μ
              ((_root_.SecondQuantization.Bosonic.annihilate i).comp
                (_root_.SecondQuantization.Bosonic.annihilate j)) = 0 := by
            simpa only [grandCanonicalGibbsExpectation, grandCanonicalAlgebraicPartition,
              imaginaryTimeEvolveFree, Common.diagonalEvolution] using
              (Common.diagonalTraceRatio_eq_zero_of_carriesShift
                ((carriesParticleNumberCharge_annihilate i).comp
                  (carriesParticleNumberCharge_annihilate j))
                (by norm_num)
                (fun n : Occupation Mode =>
                  Complex.exp (((-β) *
                    freeEigenvalue (fun k => ε k - μ) n : ℝ) : ℂ)))
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using hzero
      | create j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            (grandCanonicalGibbsExpectation_annihilate_comp_create_concrete
              ε β μ hpos i j)
  | create i =>
      cases g with
      | annihilate j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            (grandCanonicalGibbsExpectation_create_comp_annihilate_concrete
              ε β μ hpos i j)
      | create j =>
          have hzero : grandCanonicalGibbsExpectation ε β μ
              ((_root_.SecondQuantization.Bosonic.create i).comp
                (_root_.SecondQuantization.Bosonic.create j)) = 0 := by
            simpa only [grandCanonicalGibbsExpectation, grandCanonicalAlgebraicPartition,
              imaginaryTimeEvolveFree, Common.diagonalEvolution] using
              (Common.diagonalTraceRatio_eq_zero_of_carriesShift
                ((carriesParticleNumberCharge_create i).comp
                  (carriesParticleNumberCharge_create j))
                (by norm_num)
                (fun n : Occupation Mode =>
                  Complex.exp (((-β) *
                    freeEigenvalue (fun k => ε k - μ) n : ℝ) : ℂ)))
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using hzero

end
end Bosonic
end SecondQuantization

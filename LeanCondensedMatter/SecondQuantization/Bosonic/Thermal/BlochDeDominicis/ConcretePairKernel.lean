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

/-- A nonzero particle-number charge has zero free grand-canonical Gibbs expectation. -/
private theorem grandCanonicalGibbsExpectation_eq_zero_of_charge
    (ε : Mode → ℝ) (β μ : ℝ)
    {A : FockSpace Mode →ₗ[ℂ] FockSpace Mode} {q : ℤ}
    (hA : Common.CarriesShift
      (fun n : Occupation Mode => (particleNumber n : ℤ)) A q)
    (hq : q ≠ 0) :
    grandCanonicalGibbsExpectation ε β μ A = 0 := by
  simpa only [grandCanonicalGibbsExpectation, grandCanonicalAlgebraicPartition,
    imaginaryTimeEvolveFree, Common.diagonalEvolution] using
    (Common.diagonalTraceRatio_eq_zero_of_carriesShift hA hq
      (fun n : Occupation Mode =>
        Complex.exp (((-β) *
          freeEigenvalue (fun k => ε k - μ) n : ℝ) : ℂ)))

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
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            (grandCanonicalGibbsExpectation_eq_zero_of_charge ε β μ
              ((carriesParticleNumberCharge_annihilate i).comp
                (carriesParticleNumberCharge_annihilate j)) (by norm_num))
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
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue, Module.End.mul_eq_comp] using
            (grandCanonicalGibbsExpectation_eq_zero_of_charge ε β μ
              ((carriesParticleNumberCharge_create i).comp
                (carriesParticleNumberCharge_create j)) (by norm_num))

end
end Bosonic
end SecondQuantization

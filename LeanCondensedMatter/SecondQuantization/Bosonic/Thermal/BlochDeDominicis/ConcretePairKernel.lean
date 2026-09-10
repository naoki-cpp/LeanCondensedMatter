import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.ConcreteMixedTwoPoint
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Concrete realization of the free thermal pair kernel

The mixed two-point values are now analytic theorems.  The remaining same-type pairs have identically
zero diagonal coefficients, hence summable zero Gibbs numerators and zero normalized expectations.
Together these four cases identify `freeThermalPairValue` with the actual convergence-aware free
Gibbs expectation of every two-field ordered product.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality used by the concrete pair kernel. -/
local instance instDecidableEqConcretePairKernel : DecidableEq Mode := Classical.decEq Mode

/-- Domain form for the two-creator product. -/
theorem create_comp_create_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (create i).comp (create j) ∈ freeGibbsDomain ε β := by
  change freeGibbsSummable ε β ((create i).comp (create j))
  unfold freeGibbsSummable imaginaryTimeEvolveFree
  exact (summable_zero : Summable (fun _ : Occupation Mode => (0 : ℂ))).congr fun n => by
    rw [Common.matrixCoeff_diagonalEvolution_comp, matrixCoeff_create_comp_create, mul_zero]

/-- Domain form for the two-annihilator product. -/
theorem annihilate_comp_annihilate_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (annihilate i).comp (annihilate j) ∈ freeGibbsDomain ε β := by
  change freeGibbsSummable ε β ((annihilate i).comp (annihilate j))
  unfold freeGibbsSummable imaginaryTimeEvolveFree
  exact (summable_zero : Summable (fun _ : Occupation Mode => (0 : ℂ))).congr fun n => by
    rw [Common.matrixCoeff_diagonalEvolution_comp,
      matrixCoeff_annihilate_comp_annihilate, mul_zero]

/-- The normalized free-Gibbs expectation of two creators vanishes. -/
theorem freeGibbsExpectation_create_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    freeGibbsExpectation ε β ((create i).comp (create j)) = 0 := by
  unfold freeGibbsExpectation Common.tsumTrace imaginaryTimeEvolveFree
  simp_rw [Common.matrixCoeff_diagonalEvolution_comp, matrixCoeff_create_comp_create, mul_zero]
  simp

/-- The normalized free-Gibbs expectation of two annihilators vanishes. -/
theorem freeGibbsExpectation_annihilate_comp_annihilate
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    freeGibbsExpectation ε β ((annihilate i).comp (annihilate j)) = 0 := by
  unfold freeGibbsExpectation Common.tsumTrace imaginaryTimeEvolveFree
  simp_rw [Common.matrixCoeff_diagonalEvolution_comp,
    matrixCoeff_annihilate_comp_annihilate, mul_zero]
  simp

variable [Fintype Mode]

/-- Every ordered product of two free thermal fields belongs to the explicit free-Gibbs domain. -/
theorem FreeThermalField.orderedProduct_pair_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k)
    (f g : FreeThermalField Mode) :
    FreeThermalField.orderedProduct [f, g] ∈ freeGibbsDomain ε β := by
  cases f with
  | annihilate i =>
      cases g with
      | annihilate j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator] using
            annihilate_comp_annihilate_mem_freeGibbsDomain ε β i j
      | create j =>
          change freeGibbsSummable ε β
            ((_root_.SecondQuantization.Bosonic.annihilate i).comp
              (_root_.SecondQuantization.Bosonic.create j))
          exact freeGibbsSummable_annihilate_comp_create ε β hpos i j
  | create i =>
      cases g with
      | annihilate j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator] using
            create_comp_annihilate_mem_freeGibbsDomain ε β hpos j i
      | create j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator] using
            create_comp_create_mem_freeGibbsDomain ε β i j

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
            freeThermalPairValue] using
            freeGibbsExpectation_annihilate_comp_annihilate ε β i j
      | create j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue] using
            freeGibbsExpectation_annihilate_comp_create_concrete ε β hpos i j
  | create i =>
      cases g with
      | annihilate j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue] using
            freeGibbsExpectation_create_comp_annihilate_concrete ε β hpos i j
      | create j =>
          simpa [FreeThermalField.orderedProduct, FreeThermalField.operator,
            freeThermalPairValue] using
            freeGibbsExpectation_create_comp_create ε β i j

/-- Functional form of the concrete pair-kernel theorem, suitable for the generic Wick-recursion
interface. -/
theorem freeGibbsFunctional_value_orderedProduct_pair_eq_freeThermalPairValue
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k)
    (f g : FreeThermalField Mode) :
    (freeGibbsFunctional ε β hpos).value (FreeThermalField.orderedProduct [f, g]) =
      freeThermalPairValue ε β f g := by
  let hmem := FreeThermalField.orderedProduct_pair_mem_freeGibbsDomain ε β hpos f g
  rw [(freeGibbsFunctional ε β hpos).value_of_mem hmem]
  exact freeGibbsExpectation_orderedProduct_pair_eq_freeThermalPairValue ε β hpos f g

end
end Bosonic
end SecondQuantization

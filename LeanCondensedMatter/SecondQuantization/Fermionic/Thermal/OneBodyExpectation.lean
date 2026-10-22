import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization

set_option linter.style.header false

/-!
# Free thermal expectation of finite second quantization

The energies `ε` are diagonal in the specified mode basis. The expectation of `dΓ(A)` on the
full fermionic Fock space is the sum of the diagonal entries of `A`, weighted by the Fermi–Dirac
occupations. These occupations are not normalized one-particle Gibbs probabilities.
No self-adjointness of the observable or positivity of `β` is required.
-/

namespace SecondQuantization.Fermionic

open scoped BigOperators
open Lattice

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- In an energy mode basis, the free Gibbs mean of a second-quantized observable is its
one-particle diagonal weighted by the Fermi–Dirac occupations. The inverse coordinate
equivalence extracts the matrix entries of the bounded one-particle operator. -/
theorem freeGibbsDensityOperator_expectation_finiteSecondQuantization
    (ε : Mode → ℝ) (β : ℝ)
    (A : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) :
    (freeGibbsDensityOperator ε β).expectation (finiteSecondQuantization A) =
      ∑ i, ((Common.finiteHilbertOperatorAlgEquiv.symm A) (latticeKet i)) i *
        (1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)) := by
  classical
  let B := Common.finiteHilbertOperatorAlgEquiv.symm A
  change (freeGibbsDensityOperator ε β).expectation (boundedOneBodyOperator B) =
    ∑ i, (B (latticeKet i)) i * (1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1))
  have hB : B = ∑ i, ∑ j, (B (latticeKet j)) i • matrixUnit i j := by
    apply (Finsupp.basisSingleOne : Module.Basis Mode ℂ (Mode →₀ ℂ)).ext
    intro j
    ext i
    simp [LinearMap.sum_apply, Finsupp.finsetSum_apply, matrixUnit_apply, latticeKet]
  have hunit (i j : Mode) :
      (freeGibbsDensityOperator ε β).expectation
          (boundedOneBodyOperator (matrixUnit i j)) =
        if j = i then 1 / (Complex.exp ((β : ℂ) * (ε j : ℂ)) + 1) else 0 := by
    change (freeGibbsDensityOperator ε β).expectation
      (Common.finiteHilbertOperatorAlgEquiv
        (AlgebraicFock.occupationConjugate
          (Finsupp.basisSingleOne : Module.Basis Mode ℂ (Mode →₀ ℂ))
          (AlgebraicFock.dGamma ((Mode →₀ ℂ)) (matrixUnit i j)))) = _
    rw [occupationConjugate_dGamma_matrixUnit,
      freeGibbsDensityOperator_expectation_create_comp_annihilate]
  conv_lhs => rw [hB]
  simp only [map_sum, map_smul, hunit, smul_eq_mul]
  simp [mul_ite]

end
end SecondQuantization.Fermionic

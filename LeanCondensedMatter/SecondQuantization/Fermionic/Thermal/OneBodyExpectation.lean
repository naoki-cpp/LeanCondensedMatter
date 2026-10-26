import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsContraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization

set_option linter.style.header false

/-!
# Free thermal expectation of finite second quantization

The energies `ε` are diagonal in the specified mode basis. For the finite full-Fock
state with grand-canonical energy `E - μ N`, the expectation of `dΓ(A)` is the sum
of the diagonal entries of `A` weighted by Fermi–Dirac occupations at `ε - μ`.
These occupations are not normalized one-particle Gibbs probabilities.
No self-adjointness of the observable or positivity of `β` is required.
-/

namespace SecondQuantization.Fermionic

open scoped BigOperators
open _root_.SecondQuantization.Fermionic.Lattice

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- In an energy mode basis, the free Gibbs mean of a second-quantized observable is its
one-particle diagonal weighted by the Fermi–Dirac occupations. The inverse coordinate
equivalence extracts the matrix entries of the bounded one-particle operator. -/
theorem finiteGrandCanonicalGibbsDensityOperator_expectation_finiteSecondQuantization
    (ε : Mode → ℝ) (β μ : ℝ)
    (A : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) :
    (QuantumTheory.eigenbasisGibbsDensityOperator
      (Common.finiteHilbertBasis (Config := Occupation Mode))
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
      (QuantumTheory.eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)).expectation
        (finiteSecondQuantization A) =
      ∑ i, ((Common.finiteHilbertOperatorAlgEquiv.symm A) (latticeKet i)) i *
        (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1)) := by
  classical
  have hE :
      Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
        fermionEnergy (fun i => ε i - μ) := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  rw [hE]
  let ξ : Mode → ℝ := fun i => ε i - μ
  change (freeGibbsDensityOperator ξ β).expectation (finiteSecondQuantization A) =
    ∑ i, ((Common.finiteHilbertOperatorAlgEquiv.symm A) (latticeKet i)) i *
      (1 / (Complex.exp ((β : ℂ) * (ξ i : ℂ)) + 1))
  let B := Common.finiteHilbertOperatorAlgEquiv.symm A
  change (freeGibbsDensityOperator ξ β).expectation (boundedOneBodyOperator B) =
    ∑ i, (B (latticeKet i)) i * (1 / (Complex.exp ((β : ℂ) * (ξ i : ℂ)) + 1))
  have hB : B = ∑ i, ∑ j, (B (latticeKet j)) i • matrixUnit i j := by
    apply (Finsupp.basisSingleOne : Module.Basis Mode ℂ (Mode →₀ ℂ)).ext
    intro j
    ext i
    simp [LinearMap.sum_apply, Finsupp.finsetSum_apply, matrixUnit_apply, latticeKet,
      Finsupp.single_apply]
  have hunit (i j : Mode) :
      (freeGibbsDensityOperator ξ β).expectation
          (boundedOneBodyOperator (matrixUnit i j)) =
        if j = i then 1 / (Complex.exp ((β : ℂ) * (ξ j : ℂ)) + 1) else 0 := by
    change (freeGibbsDensityOperator ξ β).expectation
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

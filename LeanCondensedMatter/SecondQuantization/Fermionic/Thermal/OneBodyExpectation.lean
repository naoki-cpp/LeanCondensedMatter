import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteCompletedGibbsCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization

set_option linter.style.header false

/-!
# Free thermal expectation of one-body observables

Finite sums of completed creation-annihilation bilinears are bounded even when the mode type is
infinite. Their mean is stated through the general summability-aware completed Gibbs
expectation; the proof uses the existing grand-canonical CAR/KMS two-point theorem.
The finite second-quantization formula is transported from this same completed finite-sum mean.

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

variable {Mode : Type*} [LinearOrder Mode]

/-- The general, summability-aware completed Gibbs expectation of a one-body observable
supported on finitely many specified modes has the Fermi-weighted diagonal mean.
Neither the mode type nor the completed Fock space needs to be finite. The observable
must be a finite sum of bounded mode bilinears, not an arbitrary unbounded operator. -/
theorem grandCanonicalGibbsExpectation_sum_create_comp_annihilate
    (ε : Mode → ℝ) (β μ : ℝ) (hsum : QuantumTheory.EigenbasisGibbsSummable
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    (s : Finset Mode) (a : Mode → Mode → ℂ) :
    Common.gibbsExpectation
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β hsum
        (∑ i ∈ s, ∑ j ∈ s, a i j • (completedCreate i).comp (completedAnnihilate j)) =
      ∑ i ∈ s, a i i * (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1)) := by
  classical
  change (Common.grandCanonicalGibbsDensityOperator
      (Config := Occupation Mode) ε β μ hsum).expectation _ = _
  simp only [map_sum, map_smul,
    grandCanonicalGibbsDensityOperator_expectation_create_comp_annihilate, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_ite, hi]

variable [Fintype Mode]

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
  let E := Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ
  let hsum := QuantumTheory.eigenbasisGibbsSummable_of_finite E β
  let ρ := QuantumTheory.eigenbasisGibbsDensityOperator
    (Common.finiteHilbertBasis (Config := Occupation Mode)) E β hsum
  change ρ.expectation (finiteSecondQuantization A) =
    ∑ i, ((Common.finiteHilbertOperatorAlgEquiv.symm A) (latticeKet i)) i *
      (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1))
  let B := Common.finiteHilbertOperatorAlgEquiv.symm A
  change ρ.expectation (boundedOneBodyOperator B) =
    ∑ i, (B (latticeKet i)) i *
      (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1))
  have hB : B = ∑ i, ∑ j, (B (latticeKet j)) i • matrixUnit i j := by
    apply (Finsupp.basisSingleOne : Module.Basis Mode ℂ (Mode →₀ ℂ)).ext
    intro j
    ext i
    simp [LinearMap.sum_apply, Finsupp.finsetSum_apply, matrixUnit_apply, latticeKet,
      Finsupp.single_apply]
  have hunit (i j : Mode) :
      ρ.expectation (boundedOneBodyOperator (matrixUnit i j)) =
        Common.gibbsExpectation E β hsum
          ((completedCreate i).comp (completedAnnihilate j)) := by
    change ρ.expectation
      (Common.finiteHilbertOperatorAlgEquiv
        (AlgebraicFock.occupationConjugate
          (Finsupp.basisSingleOne : Module.Basis Mode ℂ (Mode →₀ ℂ))
          (AlgebraicFock.dGamma ((Mode →₀ ℂ)) (matrixUnit i j)))) = _
    rw [occupationConjugate_dGamma_matrixUnit]
    simpa [Common.gibbsExpectation, Common.finiteGibbsExpectation,
      Common.finiteGibbsExpectationLinearMap, ρ] using
      (Common.finiteGibbsExpectation_eq_completed_of_algebraicCore
        (Config := Occupation Mode) E β
        ((create i).comp (annihilate j)) ((completedCreate i).comp (completedAnnihilate j))
        (Common.completedProduct_comp_algebraicToCompleted_of_core
          (create i) (annihilate j) (completedCreate i) (completedAnnihilate j)
          (completedCreate_comp_algebraicToCompleted i)
          (completedAnnihilate_comp_algebraicToCompleted j)))
  conv_lhs => rw [hB]
  simp only [map_sum, map_smul, hunit]
  simpa only [map_sum, map_smul] using
    (grandCanonicalGibbsExpectation_sum_create_comp_annihilate
      ε β μ hsum Finset.univ (fun i j => (B (latticeKet j)) i))

end
end SecondQuantization.Fermionic

import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option linter.style.header false

/-!
# Finite-mode bosonic fields and number-conserving quadratic operators

Creation is linear and annihilation conjugate-linear in the one-particle vector.
All operators act on algebraic occupation Fock space. An orthonormal change of
one-particle basis preserves CCR; no completed Fock-space unitary is constructed.
-/

namespace SecondQuantization.Bosonic

open scoped BigOperators InnerProductSpace
noncomputable section
variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqFiniteModes : DecidableEq Mode := Classical.decEq Mode

/-- Creation in a one-particle vector, as a finite linear combination of site creations. -/
def createVector : EuclideanSpace ℂ Mode →ₗ[ℂ] Module.End ℂ (FockSpace Mode) where
  toFun v := ∑ i, v i • create i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

/-- Annihilation in a one-particle vector, conjugate-linear in that vector. -/
def annihilateVector (v : EuclideanSpace ℂ Mode) : Module.End ℂ (FockSpace Mode) :=
  ∑ i, star (v i) • annihilate i

theorem comm_annihilateVector_createVector (v w : EuclideanSpace ℂ Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (annihilateVector v) (createVector w) =
      inner ℂ v w • LinearMap.id := by
  classical
  change ScalarExchange.zetaCommutator (1 : ℂ)
    (∑ i, star (v i) • annihilate i) (∑ j, w j • create j) = _
  rw [ScalarExchange.zetaCommutator_sum_sum]
  simp_rw [ScalarExchange.zetaCommutator_smul_smul, comm_annihilate_create]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm, Finset.sum_smul]

theorem comm_createVector_createVector (v w : EuclideanSpace ℂ Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (createVector v) (createVector w) = 0 := by
  change ScalarExchange.zetaCommutator (1 : ℂ)
    (∑ i, v i • create i) (∑ j, w j • create j) = 0
  rw [ScalarExchange.zetaCommutator_sum_sum]
  simp_rw [ScalarExchange.zetaCommutator_smul_smul, comm_create_create]
  simp

theorem comm_annihilateVector_annihilateVector (v w : EuclideanSpace ℂ Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (annihilateVector v) (annihilateVector w) = 0 := by
  rw [annihilateVector, annihilateVector, ScalarExchange.zetaCommutator_sum_sum]
  simp_rw [ScalarExchange.zetaCommutator_smul_smul, comm_annihilate_annihilate]
  simp

/-- Finite-mode, number-conserving second quantization of a one-particle endomorphism. -/
def secondQuantization : Module.End ℂ (EuclideanSpace ℂ Mode) →ₗ[ℂ]
    Module.End ℂ (FockSpace Mode) where
  toFun T := ∑ i, ∑ j, (T (EuclideanSpace.single j 1) i) • (create i).comp (annihilate j)
  map_add' T S := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c T := by simp [Finset.smul_sum, smul_smul]

/-- Creation in a coordinate basis vector is the corresponding site creation. -/
@[simp]
theorem createVector_single (i : Mode) :
    createVector (EuclideanSpace.single i 1) = create i := by
  simp [createVector, PiLp.single_apply, ite_smul]

/-- Annihilation in a coordinate basis vector is the corresponding site annihilation. -/
@[simp]
theorem annihilateVector_single (i : Mode) :
    annihilateVector (EuclideanSpace.single i 1) = annihilate i := by
  simp [annihilateVector, PiLp.single_apply, ite_smul]

/-- A rank-one one-particle operator lifts to its normal-ordered field product. -/
@[simp]
theorem secondQuantization_rankOne (v w : EuclideanSpace ℂ Mode) :
    secondQuantization (InnerProductSpace.rankOne ℂ v w).toLinearMap =
      (createVector v).comp (annihilateVector w) := by
  have hc (i j : Mode) :
      (InnerProductSpace.rankOne ℂ v w).toLinearMap (EuclideanSpace.single j 1) i =
        v i * star (w j) := by
    change inner ℂ w (EuclideanSpace.single j 1) * v i = _
    simp [EuclideanSpace.inner_single_right, mul_comm]
  change (∑ i, ∑ j,
    ((InnerProductSpace.rankOne ℂ v w).toLinearMap (EuclideanSpace.single j 1) i) •
      (create i).comp (annihilate j)) =
    (∑ i, v i • create i).comp (∑ j, star (w j) • annihilate j)
  simp_rw [hc]
  apply LinearMap.ext
  intro ψ
  apply Finsupp.ext
  intro n
  suffices h :
      (∑ i, ∑ j, (v i * star (w j)) * ((create i) ((annihilate j) ψ)) n) =
        ∑ j, ∑ i, star (w j) * (v i * ((create i) ((annihilate j) ψ)) n) by
    simpa [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, map_smul,
      Finset.sum_apply, Finset.mul_sum] using h
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every finite orthonormal basis gives the same number-conserving quadratic operator. -/
theorem secondQuantization_eq_sum_of_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ Mode))
    (T : Module.End ℂ (EuclideanSpace ℂ Mode)) :
    secondQuantization T =
      ∑ q, (createVector (T (b q))).comp (annihilateVector (b q)) := by
  have hT : T = ∑ q, (InnerProductSpace.rankOne ℂ (T (b q)) (b q)).toLinearMap := by
    apply LinearMap.ext
    intro v
    have h := congrArg T (b.sum_repr' v)
    simpa [map_sum, map_smul, LinearMap.sum_apply] using h.symm
  conv_lhs => rw [hT, map_sum]
  simp_rw [secondQuantization_rankOne]

/-- A complete orthonormal eigenbasis diagonalizes the algebraic quadratic operator. -/
theorem secondQuantization_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ Mode))
    (T : Module.End ℂ (EuclideanSpace ℂ Mode)) (ε : ι → ℂ)
    (hT : ∀ q, T (b q) = ε q • b q) :
    secondQuantization T = ∑ q, ε q • (createVector (b q)).comp (annihilateVector (b q)) := by
  rw [secondQuantization_eq_sum_of_basis b]
  simp_rw [hT, map_smul, LinearMap.smul_comp]

end
end SecondQuantization.Bosonic

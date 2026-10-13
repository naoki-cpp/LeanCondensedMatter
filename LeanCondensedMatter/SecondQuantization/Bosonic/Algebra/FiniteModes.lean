import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator
import Mathlib.Analysis.InnerProductSpace.PiL2

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

/-- Creation in a one-particle vector, as a finite linear combination of site creations. -/
def createVector (v : EuclideanSpace ℂ Mode) : Module.End ℂ (FockSpace Mode) :=
  ∑ i, v i • create i

/-- Annihilation in a one-particle vector, conjugate-linear in that vector. -/
def annihilateVector (v : EuclideanSpace ℂ Mode) : Module.End ℂ (FockSpace Mode) :=
  ∑ i, star (v i) • annihilate i

theorem comm_annihilateVector_createVector (v w : EuclideanSpace ℂ Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (annihilateVector v) (createVector w) =
      inner ℂ v w • LinearMap.id := by
  classical
  rw [annihilateVector, createVector, ScalarExchange.zetaCommutator_sum_sum]
  simp_rw [ScalarExchange.zetaCommutator_smul_smul, comm_annihilate_create]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm, Finset.sum_smul]

theorem comm_createVector_createVector (v w : EuclideanSpace ℂ Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (createVector v) (createVector w) = 0 := by
  rw [createVector, createVector, ScalarExchange.zetaCommutator_sum_sum]
  simp_rw [ScalarExchange.zetaCommutator_smul_smul, comm_create_create]
  simp

theorem comm_annihilateVector_annihilateVector (v w : EuclideanSpace ℂ Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (annihilateVector v) (annihilateVector w) = 0 := by
  rw [annihilateVector, annihilateVector, ScalarExchange.zetaCommutator_sum_sum]
  simp_rw [ScalarExchange.zetaCommutator_smul_smul, comm_annihilate_annihilate]
  simp

/-- Finite-mode, number-conserving second quantization of a one-particle endomorphism. -/
def secondQuantization (T : Module.End ℂ (EuclideanSpace ℂ Mode)) :
    Module.End ℂ (FockSpace Mode) :=
  ∑ i, ∑ j, (T (EuclideanSpace.single j 1) i) • (create i).comp (annihilate j)

/-- A complete orthonormal eigenbasis diagonalizes the algebraic quadratic operator. -/
theorem secondQuantization_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ Mode))
    (T : Module.End ℂ (EuclideanSpace ℂ Mode)) (ε : ι → ℂ)
    (hT : ∀ q, T (b q) = ε q • b q) :
    secondQuantization T = ∑ q, ε q • (createVector (b q)).comp (annihilateVector (b q)) := by
  have hc (i j : Mode) :
      T (EuclideanSpace.single j 1) i = ∑ q, ε q * b q i * star (b q j) := by
    have h := congrArg (fun v => T v i) (b.sum_repr' (EuclideanSpace.single j 1))
    simp only [map_sum, map_smul, hT, EuclideanSpace.inner_single_right,
      one_mul, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold secondQuantization
  simp_rw [hc, Finset.sum_smul]
  calc
    _ = ∑ i, ∑ q, ∑ j, (ε q * b q i * star (b q j)) •
        (create i).comp (annihilate j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ q, ∑ i, ∑ j, (ε q * b q i * star (b q j)) •
        (create i).comp (annihilate j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply LinearMap.ext
      intro ψ
      apply Finsupp.ext
      intro n
      simp [createVector, annihilateVector, LinearMap.sum_apply, map_sum,
        Finset.sum_apply, map_smul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end
end SecondQuantization.Bosonic

import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option linter.style.header false

/-!
# Analytic properties of completed fermionic diagonal operators

This file develops analytic properties of the maximal weighted diagonal operators defined in
`Diagonal.lean`. The definition layer stays independent of adjoints and closed-operator theory;
this file begins that later analytic layer.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- Every maximal weighted diagonal domain contains the dense finite-support algebraic core. -/
theorem completedDiagonalDomain_dense (w : Occupation Mode → ℂ) :
    Dense ((completedDiagonalDomain w : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  apply Dense.mono ?_ algebraicToCompleted_denseRange
  rintro _ ⟨x, rfl⟩
  exact algebraicToCompleted_mem_completedDiagonalDomain w x

/-- The `LinearPMap` diagonal operator is densely defined for every weight. -/
theorem completedDiagonalOperator_denseDomain (w : Occupation Mode → ℂ) :
    Dense (((completedDiagonalOperator w).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  exact completedDiagonalDomain_dense w

/-- Membership in the graph of the maximal diagonal operator is exactly the coordinatewise
multiplication equation. The converse uses maximality of the weighted `ℓ²` domain: if the proposed
output already lies in `ℓ²`, then the weighted input automatically belongs to the domain. -/
theorem mem_completedDiagonalOperator_graph_iff (w : Occupation Mode → ℂ)
    (z : CompletedFockSpace Mode × CompletedFockSpace Mode) :
    z ∈ (completedDiagonalOperator w).graph ↔
      ∀ n : Occupation Mode, z.2 n = w n * z.1 n := by
  constructor
  · intro hz n
    rw [LinearPMap.mem_graph_iff] at hz
    obtain ⟨x, hx, hfx⟩ := hz
    calc
      z.2 n = (completedDiagonalOperator w x) n :=
        (congrArg (fun ψ : CompletedFockSpace Mode => ψ n) hfx).symm
      _ = w n * (x : CompletedFockSpace Mode) n := completedDiagonalOperator_apply w x n
      _ = w n * z.1 n := by rw [hx]
  · intro hz
    have hdomain : z.1 ∈ completedDiagonalDomain w := by
      rw [mem_completedDiagonalDomain_iff]
      have hout := lp.memℓp z.2
      convert hout using 1
      funext n
      exact (hz n).symm
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨z.1, hdomain⟩, rfl, ?_⟩
    apply lp.ext
    funext n
    rw [completedDiagonalOperator_apply]
    exact (hz n).symm

/-- A maximal diagonal multiplication operator is closed for an arbitrary complex weight. -/
theorem completedDiagonalOperator_isClosed (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      ((completedDiagonalOperator w).graph :
        Set (CompletedFockSpace Mode × CompletedFockSpace Mode)) =
        ⋂ n : Occupation Mode,
          {z : CompletedFockSpace Mode × CompletedFockSpace Mode |
            z.2 n = w n * z.1 n} := by
    ext z
    rw [Set.mem_iInter]
    exact mem_completedDiagonalOperator_graph_iff w z
  rw [hgraph]
  apply isClosed_iInter
  intro n
  apply isClosed_eq
  · exact (lp.evalCLM ℂ (fun _ : Occupation Mode => ℂ) 2 n).continuous.comp continuous_snd
  · exact continuous_const.mul
      ((lp.evalCLM ℂ (fun _ : Occupation Mode => ℂ) 2 n).continuous.comp continuous_fst)

/-- Every maximal diagonal operator is therefore closable, without any reality assumption. -/
theorem completedDiagonalOperator_isClosable (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).IsClosable :=
  (completedDiagonalOperator_isClosed w).isClosable

/-- A diagonal operator whose weights are fixed by complex conjugation is formally symmetric. -/
theorem completedDiagonalOperator_isFormalAdjoint_self (w : Occupation Mode → ℂ)
    (hw : ∀ n, star (w n) = w n) :
    (completedDiagonalOperator w).IsFormalAdjoint (completedDiagonalOperator w) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [completedDiagonalOperator_apply, completedDiagonalOperator_apply]
  have hwn : (starRingEnd ℂ) (w n) = w n := by
    simpa using hw n
  simp [hwn, mul_assoc, mul_left_comm]

/-- Free-Hamiltonian occupation energies are fixed by complex conjugation. -/
theorem star_freeHamiltonianWeight (ε : Mode → ℝ) (n : Occupation Mode) :
    star (freeHamiltonianWeight ε n) = freeHamiltonianWeight ε n := by
  simp [freeHamiltonianWeight]

/-- The completed free Hamiltonian is densely defined. -/
theorem completedFreeHamiltonian_denseDomain (ε : Mode → ℝ) :
    Dense (((completedFreeHamiltonian ε).domain : Submodule ℂ (CompletedFockSpace Mode)) :
      Set (CompletedFockSpace Mode)) := by
  exact completedDiagonalOperator_denseDomain (freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is closed. -/
theorem completedFreeHamiltonian_isClosed (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsClosed := by
  exact completedDiagonalOperator_isClosed (freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is formally symmetric. -/
theorem completedFreeHamiltonian_isFormalAdjoint_self (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsFormalAdjoint (completedFreeHamiltonian ε) := by
  exact completedDiagonalOperator_isFormalAdjoint_self (freeHamiltonianWeight ε)
    (star_freeHamiltonianWeight ε)

/-- The completed free Hamiltonian is closable. -/
theorem completedFreeHamiltonian_isClosable (ε : Mode → ℝ) :
    (completedFreeHamiltonian ε).IsClosable :=
  (completedFreeHamiltonian_isClosed ε).isClosable

/-- Total-particle-number weights are fixed by complex conjugation. -/
theorem star_particleNumberWeight (n : Occupation Mode) :
    star (particleNumber n : ℂ) = (particleNumber n : ℂ) := by
  simp

/-- The completed total number operator is densely defined. -/
theorem completedTotalNumberOperator_denseDomain {Mode : Type*} :
    Dense (((completedTotalNumberOperator (Mode := Mode)).domain :
      Submodule ℂ (CompletedFockSpace Mode)) : Set (CompletedFockSpace Mode)) := by
  exact completedDiagonalOperator_denseDomain
    (fun n : Occupation Mode => (particleNumber n : ℂ))

/-- The completed total number operator is closed. -/
theorem completedTotalNumberOperator_isClosed {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsClosed := by
  exact completedDiagonalOperator_isClosed
    (fun n : Occupation Mode => (particleNumber n : ℂ))

/-- The completed total number operator is formally symmetric. -/
theorem completedTotalNumberOperator_isFormalAdjoint_self {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsFormalAdjoint
      (completedTotalNumberOperator (Mode := Mode)) := by
  exact completedDiagonalOperator_isFormalAdjoint_self
    (fun n : Occupation Mode => (particleNumber n : ℂ))
    (star_particleNumberWeight (Mode := Mode))

/-- The completed total number operator is closable. -/
theorem completedTotalNumberOperator_isClosable {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsClosable :=
  (completedTotalNumberOperator_isClosed (Mode := Mode)).isClosable

end
end Fermionic
end SecondQuantization

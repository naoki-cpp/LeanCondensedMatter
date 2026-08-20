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

/-- The maximal diagonal operator with conjugated weights is a formal adjoint of the original
operator. -/
theorem completedDiagonalOperator_isFormalAdjoint_conj (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).IsFormalAdjoint
      (completedDiagonalOperator fun n => star (w n)) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [completedDiagonalOperator_apply, completedDiagonalOperator_apply]
  simp [mul_assoc, mul_left_comm]

/-- The conjugate-weight diagonal operator is contained in the Hilbert-space adjoint. -/
theorem completedDiagonalOperator_conj_le_adjoint (w : Occupation Mode → ℂ) :
    completedDiagonalOperator (fun n => star (w n)) ≤
      (completedDiagonalOperator w).adjoint := by
  exact (completedDiagonalOperator_isFormalAdjoint_conj w).le_adjoint
    (completedDiagonalOperator_denseDomain w)

/-- The adjoint acts coordinatewise by the conjugated diagonal weight. -/
theorem completedDiagonalOperator_adjoint_apply (w : Occupation Mode → ℂ)
    (y : (completedDiagonalOperator w).adjoint.domain) (n : Occupation Mode) :
    (completedDiagonalOperator w).adjoint y n =
      star (w n) * (y : CompletedFockSpace Mode) n := by
  let e : (completedDiagonalOperator w).domain :=
    ⟨completedBasisState n, completedBasisState_mem_completedDiagonalDomain w n⟩
  have h := ((completedDiagonalOperator w).adjoint_isFormalAdjoint
    (completedDiagonalOperator_denseDomain w)).symm e y
  have he : completedDiagonalOperator w e = w n • completedBasisState n := by
    exact completedDiagonalOperator_basisState w n
  rw [he] at h
  change inner ℂ (w n • completedBasisState n) (y : CompletedFockSpace Mode) =
    inner ℂ (completedBasisState n) ((completedDiagonalOperator w).adjoint y) at h
  rw [inner_smul_left, inner_completedBasisState_left, inner_completedBasisState_left] at h
  exact h.symm

/-- Every vector in the adjoint domain belongs to the conjugate-weight maximal diagonal domain. -/
theorem completedDiagonalOperator_adjoint_domain_le_conj (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).adjoint.domain ≤
      completedDiagonalDomain (fun n => star (w n)) := by
  intro y hy
  rw [mem_completedDiagonalDomain_iff]
  let y' : (completedDiagonalOperator w).adjoint.domain := ⟨y, hy⟩
  have hout := lp.memℓp ((completedDiagonalOperator w).adjoint y')
  convert hout using 1
  funext n
  exact (completedDiagonalOperator_adjoint_apply w y' n).symm

/-- The Hilbert-space adjoint is contained in the conjugate-weight maximal diagonal operator. -/
theorem completedDiagonalOperator_adjoint_le_conj (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).adjoint ≤
      completedDiagonalOperator (fun n => star (w n)) := by
  refine ⟨completedDiagonalOperator_adjoint_domain_le_conj w, ?_⟩
  intro x y hxy
  apply lp.ext
  funext n
  rw [completedDiagonalOperator_adjoint_apply, completedDiagonalOperator_apply]
  change star (w n) * (x : CompletedFockSpace Mode) n =
    star (w n) * (y : CompletedFockSpace Mode) n
  rw [hxy]

/-- The adjoint of a maximal diagonal multiplication operator is exactly multiplication by the
complex-conjugated weight, with the corresponding maximal weighted `ℓ²` domain. -/
theorem completedDiagonalOperator_adjoint_eq (w : Occupation Mode → ℂ) :
    (completedDiagonalOperator w).adjoint =
      completedDiagonalOperator (fun n => star (w n)) := by
  exact le_antisymm (completedDiagonalOperator_adjoint_le_conj w)
    (completedDiagonalOperator_conj_le_adjoint w)

/-- A diagonal operator whose weights are fixed by complex conjugation is formally symmetric. -/
theorem completedDiagonalOperator_isFormalAdjoint_self (w : Occupation Mode → ℂ)
    (hw : ∀ n, star (w n) = w n) :
    (completedDiagonalOperator w).IsFormalAdjoint (completedDiagonalOperator w) := by
  have h := completedDiagonalOperator_isFormalAdjoint_conj w
  have hwfun : (fun n => star (w n)) = w := funext hw
  rw [hwfun] at h
  exact h

/-- A maximal diagonal operator with conjugation-fixed weights is self-adjoint. -/
theorem completedDiagonalOperator_isSelfAdjoint_of_star (w : Occupation Mode → ℂ)
    (hw : ∀ n, star (w n) = w n) :
    IsSelfAdjoint (completedDiagonalOperator w) := by
  rw [LinearPMap.isSelfAdjoint_def, completedDiagonalOperator_adjoint_eq]
  congr 1
  funext n
  exact hw n

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

/-- The completed free Hamiltonian is self-adjoint. -/
theorem completedFreeHamiltonian_isSelfAdjoint (ε : Mode → ℝ) :
    IsSelfAdjoint (completedFreeHamiltonian ε) := by
  exact completedDiagonalOperator_isSelfAdjoint_of_star (freeHamiltonianWeight ε)
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

/-- The completed total number operator is self-adjoint. -/
theorem completedTotalNumberOperator_isSelfAdjoint {Mode : Type*} :
    IsSelfAdjoint (completedTotalNumberOperator (Mode := Mode)) := by
  exact completedDiagonalOperator_isSelfAdjoint_of_star
    (fun n : Occupation Mode => (particleNumber n : ℂ))
    (star_particleNumberWeight (Mode := Mode))

/-- The completed total number operator is closable. -/
theorem completedTotalNumberOperator_isClosable {Mode : Type*} :
    (completedTotalNumberOperator (Mode := Mode)).IsClosable :=
  (completedTotalNumberOperator_isClosed (Mode := Mode)).isClosable

end
end Fermionic
end SecondQuantization

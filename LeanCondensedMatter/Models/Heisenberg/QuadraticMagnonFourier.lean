import LeanCondensedMatter.Models.Heisenberg.QuadraticMagnon
import LeanCondensedMatter.Analysis.Fourier.CyclicLaplacian
import LeanCondensedMatter.Analysis.Fourier.FiniteCyclic
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FiniteModes
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.OneParticle

set_option linter.style.header false

/-!
# Fourier diagonalization of the quadratic magnon ring

The Fourier creation has positive exponent and annihilation negative exponent.
The coefficient is the bond-once energy with exchange J(2s), rather than the
directed-neighbor coefficient of the source. Source: Stancil-Prabhakar,
Section 2.7.1, equations (2.157)-(2.166).
These are identities of endomorphisms of unrestricted algebraic Fock space.
-/

namespace Models.Heisenberg.QuadraticMagnon

open SecondQuantization SecondQuantization.Bosonic
open scoped BigOperators InnerProductSpace
noncomputable section
variable {N : ℕ} [NeZero N]


/-- The normalized Fourier fields obey the mixed bosonic CCR on the algebraic domain. -/
theorem comm_fourier_annihilate_create (q r : ZMod N) :
    ScalarExchange.zetaCommutator (1 : ℂ)
      (annihilateVector (ZMod.fourierBasis q)) (createVector (ZMod.fourierBasis r)) =
      if q = r then LinearMap.id else 0 := by
  classical
  rw [comm_annihilateVector_createVector]
  rw [ZMod.fourierBasis_apply, ZMod.fourierBasis_apply,
    orthonormal_iff_ite.mp ZMod.orthonormal_fourierMode]
  split_ifs <;> simp

private theorem sum_shift {A : Type*} [AddCommMonoid A] (f : ZMod N → A) :
    (∑ i : ZMod N, f (i + 1)) = ∑ i : ZMod N, f i := by
  let e : Equiv.Perm (ZMod N) :=
    { toFun := fun i => i + 1
      invFun := fun i => i - 1
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  exact Equiv.sum_comp e f

/-- The site quadratic operator is the second quantization of the periodic Laplacian.
At 2s=1 its one-particle operator is the exact spin ring's one-magnon restriction. -/
theorem excitationHamiltonian_eq_secondQuantization (J : ℝ) (twiceSpin : ℕ) :
    excitationHamiltonian (N := N) J twiceSpin =
      secondQuantization (ZMod.cyclicLaplacian (J * twiceSpin)) := by
  classical
  have hn := sum_shift (N := N) (fun i => numberOperator i)
  have hh : (∑ i : ZMod N, (create (i - 1)).comp (annihilate i)) =
      ∑ i : ZMod N, (create i).comp (annihilate (i + 1)) := by
    simpa using (sum_shift (N := N) (fun i => (create (i - 1)).comp (annihilate i))).symm
  rw [secondQuantization_eq_sum_of_basis (EuclideanSpace.basisFun (ZMod N) ℂ)]
  simp_rw [EuclideanSpace.basisFun_apply, ZMod.cyclicLaplacian_single,
    map_smul, map_add, map_sub, createVector_single, annihilateVector_single,
    LinearMap.add_comp, LinearMap.sub_comp, LinearMap.smul_comp]
  push_cast
  simp only [← numberOperator]
  simp only [excitationHamiltonian, excitationBond, smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hn, hh]
  module

/-- Complete finite Fourier diagonalization of the quadratic excitation operator.
The summands are energy times Fourier-mode number operators. -/
theorem excitationHamiltonian_eq_sum_fourier (J : ℝ) (twiceSpin : ℕ) :
    excitationHamiltonian (N := N) J twiceSpin =
      ∑ q : ZMod N, (ZMod.cyclicLaplacianEigenvalue (J * twiceSpin) q : ℂ) •
        (createVector (ZMod.fourierBasis q)).comp (annihilateVector (ZMod.fourierBasis q)) := by
  rw [excitationHamiltonian_eq_secondQuantization]
  exact secondQuantization_eq_sum_of_eigenbasis ZMod.fourierBasis _ _
    (ZMod.cyclicLaplacian_fourierBasis (J * twiceSpin))

/-- The quadratic ring acts on embedded one-boson amplitudes by its cyclic Laplacian.
At twiceSpin = 1 this is the same amplitude operator as the exact spin-1/2 one-magnon restriction. -/
theorem excitationHamiltonian_comp_oneParticleEmbedding (J : ℝ) (twiceSpin : ℕ) :
    (excitationHamiltonian (N := N) J twiceSpin).comp oneParticleEmbedding =
      oneParticleEmbedding.comp (ZMod.cyclicLaplacian (J * twiceSpin)) := by
  rw [excitationHamiltonian_eq_secondQuantization]
  exact secondQuantization_comp_oneParticleEmbedding _

/-- Embedded Fourier amplitudes are actual one-boson eigenstates of the quadratic ring. -/
theorem excitationHamiltonian_oneParticle_fourierBasis (J : ℝ) (twiceSpin : ℕ) (q : ZMod N) :
    excitationHamiltonian J twiceSpin (oneParticleEmbedding (ZMod.fourierBasis q)) =
      (ZMod.cyclicLaplacianEigenvalue (J * twiceSpin) q : ℂ) •
        oneParticleEmbedding (ZMod.fourierBasis q) := by
  have h := LinearMap.congr_fun
    (excitationHamiltonian_comp_oneParticleEmbedding (N := N) J twiceSpin) (ZMod.fourierBasis q)
  change excitationHamiltonian J twiceSpin (oneParticleEmbedding (ZMod.fourierBasis q)) =
    oneParticleEmbedding (ZMod.cyclicLaplacian (J * twiceSpin) (ZMod.fourierBasis q)) at h
  rw [ZMod.cyclicLaplacian_fourierBasis, map_smul] at h
  exact h

end
end Models.Heisenberg.QuadraticMagnon

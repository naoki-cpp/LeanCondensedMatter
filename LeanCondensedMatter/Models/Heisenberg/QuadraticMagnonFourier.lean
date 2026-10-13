import LeanCondensedMatter.Models.Heisenberg.QuadraticMagnon
import LeanCondensedMatter.Models.Heisenberg.SpinWaveSpectrum
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FiniteModes

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

local instance : DecidableEq (ZMod N) := Classical.decEq _

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
At 2s=1 its one-particle operator is exactly the operator used in SW2. -/
theorem excitationHamiltonian_eq_secondQuantization (J : ℝ) (twiceSpin : ℕ) :
    excitationHamiltonian (N := N) J twiceSpin =
      secondQuantization (oneMagnonLaplacian (J * twiceSpin)) := by
  classical
  have hn := sum_shift (N := N) (fun i => numberOperator i)
  have hh : (∑ i : ZMod N, (create (i + 1)).comp (annihilate i)) =
      ∑ i : ZMod N, (create i).comp (annihilate (i - 1)) := by
    simpa using sum_shift (N := N) (fun i => (create i).comp (annihilate (i - 1)))
  have hrow (i : ZMod N) :
      (∑ j : ZMod N, oneMagnonLaplacian (J * twiceSpin) (EuclideanSpace.single j 1) i •
        (create i).comp (annihilate j)) =
      ((J : ℂ) * twiceSpin) • ((2 : ℂ) • numberOperator i -
        (create i).comp (annihilate (i - 1)) - (create i).comp (annihilate (i + 1))) := by
    apply LinearMap.ext
    intro ψ
    apply Finsupp.ext
    intro n
    simp [oneMagnonLaplacian, PiLp.single_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, numberOperator,
      LinearMap.sum_apply, Finset.sum_apply]
    ring
  unfold secondQuantization
  simp_rw [hrow]
  simp only [excitationHamiltonian, excitationBond, smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hn, hh]
  module

/-- Complete finite Fourier diagonalization of the quadratic excitation operator.
The summands are energy times Fourier-mode number operators. -/
theorem excitationHamiltonian_eq_sum_fourier (J : ℝ) (twiceSpin : ℕ) :
    excitationHamiltonian (N := N) J twiceSpin =
      ∑ q : ZMod N, (oneMagnonEnergy (J * twiceSpin) q : ℂ) •
        (createVector (ZMod.fourierBasis q)).comp (annihilateVector (ZMod.fourierBasis q)) := by
  rw [excitationHamiltonian_eq_secondQuantization]
  exact secondQuantization_eq_sum_of_eigenbasis ZMod.fourierBasis _ _
    (oneMagnonLaplacian_fourierBasis (J * twiceSpin))

end
end Models.Heisenberg.QuadraticMagnon

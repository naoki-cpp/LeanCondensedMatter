import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnitaryLift
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.SmearedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.OneBodyExpectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Density
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.RetardedSusceptibility
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SplitIfs

set_option linter.style.header false

/-!
# One-particle reduction of fermionic current response

Finite sums of creation-annihilation bilinears have a bounded response even on an infinite-mode
Fock space. Under lifted one-particle dynamics their commutator response depends only on the
state's two-point function; no four-point factorization is required. The finite-lattice result
rewrites the existing flux response under an explicit quadratic-dynamics condition and the
existing Fermi-weighted one-body mean. It does not replace the general interacting response,
include contact terms, or assert a continuum or thermodynamic limit.
-/

namespace SecondQuantization.Fermionic.Transport

open QuantumTheory.LinearResponse
open _root_.SecondQuantization.Fermionic.Lattice
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- Finite-rank one-body susceptibility on completed Fock space reduces to the one-particle
two-point function. The mode type may be infinite and coefficient vectors may have infinite support.
The one-particle covariance `C` is not a normalized one-particle density matrix. -/
theorem commutatorSusceptibility_completed_bilinear_sum
    {ι κ : Type*}
    (U : Multiplicative ℝ →* unitary (Common.CompletedFock Mode →L[ℂ] Common.CompletedFock Mode))
    (expectation : NormalizedExpectation (CompletedFockSpace Mode)) (hbar : ℝ)
    (C : Common.CompletedFock Mode →L[ℂ] Common.CompletedFock Mode)
    (hmean : ∀ f g, expectation (completedCreateField f * star (completedCreateField g)) =
      inner ℂ g (C f))
    (s : Finset ι) (r : Finset κ) (a : ι → ℂ) (b : κ → ℂ)
    (f g : ι → Common.CompletedFock Mode) (u v : κ → Common.CompletedFock Mode)
    (t q : ℝ) :
    let R := fun z : ℝ => (Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd z))).symm
    commutatorSusceptibility (completedFockUnitaryGroup U) hbar expectation
      (∑ i ∈ s, a i • (completedCreateField (f i) * star (completedCreateField (g i))))
      (∑ j ∈ r, b j • (completedCreateField (u j) * star (completedCreateField (v j)))) t q =
    (Complex.I / (hbar : ℂ)) * ∑ i ∈ s, ∑ j ∈ r, (a i * b j) *
      (inner ℂ (R t (g i)) (R q (u j)) * inner ℂ (R q (v j)) (C (R t (f i))) -
        inner ℂ (R q (v j)) (R t (f i)) * inner ℂ (R t (g i)) (C (R q (u j)))) := by
  classical
  dsimp only
  have hbilinear (f g u v : Common.CompletedFock Mode) :
      ⁅completedCreateField f * star (completedCreateField g),
        completedCreateField u * star (completedCreateField v)⁆ =
      inner ℂ g u • (completedCreateField f * star (completedCreateField v)) -
        inner ℂ v f • (completedCreateField u * star (completedCreateField g)) := by
    have hgu : star (completedCreateField g) * completedCreateField u =
        inner ℂ g u • (1 : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) -
          completedCreateField u * star (completedCreateField g) := by
      apply eq_sub_of_add_eq
      simpa only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add] using
        completedAnticomm_adjoint_createField g u
    have hvf : star (completedCreateField v) * completedCreateField f =
        inner ℂ v f • (1 : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) -
          completedCreateField f * star (completedCreateField v) := by
      apply eq_sub_of_add_eq
      simpa only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add] using
        completedAnticomm_adjoint_createField v f
    have hcc : completedCreateField u * completedCreateField f =
        -(completedCreateField f * completedCreateField u) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add] using
        completedAnticomm_createField_createField u f
    have haa : star (completedCreateField v) * star (completedCreateField g) =
        -(star (completedCreateField g) * star (completedCreateField v)) := by
      apply eq_neg_iff_add_eq_zero.mpr
      have h := congrArg star (completedAnticomm_createField_createField g v)
      simpa only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add,
        star_add, star_mul, star_zero] using h
    have hquartic : completedCreateField u * completedCreateField f *
        (star (completedCreateField v) * star (completedCreateField g)) =
        completedCreateField f * completedCreateField u *
          (star (completedCreateField g) * star (completedCreateField v)) := by
      rw [hcc, haa, neg_mul, mul_neg, neg_neg]
    simp only [mul_assoc] at hquartic
    change (completedCreateField f * star (completedCreateField g)) *
        (completedCreateField u * star (completedCreateField v)) -
      (completedCreateField u * star (completedCreateField v)) *
        (completedCreateField f * star (completedCreateField g)) = _
    calc
      _ = completedCreateField f * (star (completedCreateField g) * completedCreateField u) *
            star (completedCreateField v) -
          completedCreateField u * (star (completedCreateField v) * completedCreateField f) *
            star (completedCreateField g) := by noncomm_ring
      _ = _ := by
        rw [hgu, hvf]
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc]
        rw [hquartic]
        abel
  have hcreate (z : ℝ) (w : Common.CompletedFock Mode) :
      heisenbergEvolution (completedFockUnitaryGroup U) z (completedCreateField w) =
        completedCreateField ((Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd z))).symm w) := by
    let e := Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd z))
    rw [heisenbergEvolution_apply]
    apply ContinuousLinearMap.ext
    intro x
    change (star (completedFockUnitary e : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) *
      completedCreateField w * (completedFockUnitary e :
        CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)) x = _
    rw [LinearIsometryEquiv.star_eq_symm]
    have h := completedFockUnitary_createField e (e.symm w) x
    rw [e.apply_symm_apply] at h
    have h' := congrArg (completedFockUnitary e).symm h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h'.symm
  unfold commutatorSusceptibility
  simp only [map_sum, map_smul, map_mul, map_star, hcreate]
  have hsum := ScalarExchange.zetaCommutator_sum_sum (1 : ℂ) s r
    (fun i => a i • (completedCreateField
      ((Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd t))).symm (f i)) *
      star (completedCreateField ((Unitary.linearIsometryEquiv
        (U (Multiplicative.ofAdd t))).symm (g i)))))
    (fun j => b j • (completedCreateField
      ((Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd q))).symm (u j)) *
      star (completedCreateField ((Unitary.linearIsometryEquiv
        (U (Multiplicative.ofAdd q))).symm (v j)))))
  simp only [ScalarExchange.zetaCommutator_smul_smul,
    ScalarExchange.zetaCommutator, one_smul,
    ← LieRing.of_associative_ring_bracket] at hsum
  rw [hsum]
  simp only [hbilinear, map_sum, map_smul, map_sub, hmean, smul_eq_mul]

section FiniteLattice

variable [Fintype Mode]

/-- Under quadratic dynamics, the full finite-Fock susceptibility is the one-body mean of
the evolved one-particle commutator. The one-body mean is not required to be normalized. -/
theorem commutatorSusceptibility_finiteSecondQuantization
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Mode))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Mode))
    (generator : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode)
    (hgen : schrodingerGenerator system = finiteSecondQuantization generator)
    (mean : (EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) → ℂ)
    (hmean : ∀ A, expectation (finiteSecondQuantization A) = mean A)
    (A B : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) (t s : ℝ) :
    commutatorSusceptibility (freePropagatorGroup system) system.hbar expectation
      (finiteSecondQuantization A) (finiteSecondQuantization B) t s =
      (Complex.I / (system.hbar : ℂ)) * mean
        ⁅NormedSpace.exp (-(t • generator)) * A * NormedSpace.exp (t • generator),
          NormedSpace.exp (-(s • generator)) * B * NormedSpace.exp (s • generator)⁆ := by
  have hevolve (z : ℝ) (a : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) :
      heisenbergEvolution (freePropagatorGroup system) z (finiteSecondQuantization a) =
        finiteSecondQuantization
          (NormedSpace.exp (-(z • generator)) * a * NormedSpace.exp (z • generator)) := by
    rw [heisenbergEvolution_freePropagatorGroup_apply]
    unfold freePropagator
    rw [hgen]
    have h := finiteSecondQuantization_exp_conjugate (-generator) a z
    simpa only [map_neg, smul_neg, neg_neg, neg_smul] using h.symm
  unfold commutatorSusceptibility
  rw [hevolve, hevolve, ← finiteSecondQuantization_lie, hmean]

/-- The existing causal lattice flux response, for quadratic dynamics and a diagonal
grand-canonical initial state, reduces to a Fermi-weighted one-particle commutator.
The energies defining the state need not match the dynamical generator; equilibrium requires
that additional physical identification. Contact and conductivity normalization remain separate. -/
theorem boundedFluxRetardedResponse_eq_fermiWeighted_oneBody
    {Test : Type*} [AddCommGroup Test] [Module ℂ Test]
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Mode))
    (generator : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode)
    (hgen : schrodingerGenerator system = finiteSecondQuantization generator)
    (ε : Mode → ℝ) (β μ : ℝ)
    (source : (Mode →₀ ℂ) →ₗ[ℂ] (Mode →₀ ℂ))
    (Φ : Test →ₗ[ℂ] ((Mode →₀ ℂ) →ₗ[ℂ] (Mode →₀ ℂ))) (f : Test) (t : ℝ) :
    let ρ := QuantumTheory.eigenbasisGibbsDensityOperator
      (Common.finiteHilbertBasis (Config := Occupation Mode))
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
      (QuantumTheory.eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
    let e := Common.finiteHilbertOperatorAlgEquiv (Config := Mode)
    boundedFluxRetardedResponse system ρ.toNormalizedExpectation
      (boundedOneBodyOperator source) Φ t 0 f =
      if 0 ≤ t then (Complex.I / (system.hbar : ℂ)) *
        ∑ i, ((e.symm
          ⁅NormedSpace.exp (-(t • generator)) * e (Φ f) * NormedSpace.exp (t • generator),
            e source⁆) (latticeKet i)) i *
          (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1))
      else 0 := by
  classical
  dsimp only
  let ρ := QuantumTheory.eigenbasisGibbsDensityOperator
    (Common.finiteHilbertBasis (Config := Occupation Mode))
    (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β
    (QuantumTheory.eigenbasisGibbsSummable_of_finite
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)
  let e := Common.finiteHilbertOperatorAlgEquiv (Config := Mode)
  let mean (A : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) : ℂ :=
    ∑ i, ((e.symm A) (latticeKet i)) i *
      (1 / (Complex.exp ((β : ℂ) * ((ε i - μ : ℝ) : ℂ)) + 1))
  have hmean (A : EuclideanSpace ℂ Mode →L[ℂ] EuclideanSpace ℂ Mode) :
      ρ.toNormalizedExpectation (finiteSecondQuantization A) = mean A := by
    exact finiteGrandCanonicalGibbsDensityOperator_expectation_finiteSecondQuantization ε β μ A
  have hreal (A : (Mode →₀ ℂ) →ₗ[ℂ] (Mode →₀ ℂ)) :
      finiteSecondQuantization (e A) = boundedOneBodyOperator A := by
    change boundedOneBodyOperator (e.symm (e A)) = _
    rw [e.symm_apply_apply]
  change retardedSusceptibility (freePropagatorGroup system) system.hbar
    ρ.toNormalizedExpectation (boundedOneBodyOperator (Φ f)) (boundedOneBodyOperator source) t 0 = _
  rw [← hreal (Φ f), ← hreal source]
  unfold retardedSusceptibility
  split_ifs with ht
  · rw [commutatorSusceptibility_finiteSecondQuantization system ρ.toNormalizedExpectation
      generator hgen mean hmean]
    simp only [zero_smul, neg_zero, NormedSpace.exp_zero, one_mul, mul_one]
  · rfl

end FiniteLattice

end
end SecondQuantization.Fermionic.Transport

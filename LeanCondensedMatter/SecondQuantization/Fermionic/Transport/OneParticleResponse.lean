import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.FrequencyDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Table

set_option linter.style.header false

/-! # One-electron Kubo response in the full finite Fock space

A normalized eigenvector of the one-body Hamiltonian defines a physical
rank-one stationary state of the second-quantized Hamiltonian. The
one-particle restriction of bounded second quantization and its Lie
homomorphism property identify the full-Fock causal kernel with the
one-particle kernel. For a supplied finite energy eigenbasis with one
occupied level, the existing Lehmann table evaluates this response.
No diagonalization or thermodynamic limit is assumed.
-/

namespace SecondQuantization.Fermionic.Transport

open QuantumTheory QuantumTheory.LinearResponse
open _root_.SecondQuantization.Fermionic.Lattice

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- The physical one-electron state in the actual finite lattice Fock space. -/
def oneParticleFockState (ψ : StateVector (EuclideanSpace ℂ Site)) :
    StateVector (FiniteLatticeHilbertFock Site) :=
  ⟨AlgebraicFock.finiteHilbertOneParticleEmbedding
      (Common.finiteHilbertOrthonormalBasis (Config := Site)) ψ.1,
    by simp only [LinearIsometry.norm_map, ψ.2]⟩

/-- A one-body energy eigenvector lifts to a stationary pure Fock state. -/
theorem isStationary_oneParticleFockState
    (one : BoundedFreeSystem (EuclideanSpace ℂ Site))
    (many : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (hH : many.hamiltonian.1 = finiteSecondQuantization one.hamiltonian.1)
    (ψ : StateVector (EuclideanSpace ℂ Site)) (energy : ℝ)
    (hψ : one.hamiltonian.1 ψ.1 = (energy : ℂ) • ψ.1) :
    IsStationary (freePropagatorGroup many)
      (QuantumTheory.pure (oneParticleFockState ψ)).toNormalizedExpectation := by
  apply isStationary_pure_of_eigenvector many _ energy
  let j := AlgebraicFock.finiteHilbertOneParticleEmbedding
    (Common.finiteHilbertOrthonormalBasis (Config := Site))
  change many.hamiltonian.1 (j ψ.1) = (energy : ℂ) • j ψ.1
  rw [hH, finiteSecondQuantization_apply_oneParticle, hψ, map_smul]

/-- Bounded Heisenberg evolution of a second-quantized one-body observable
is the second quantization of the original one-body evolution. -/
theorem finiteSecondQuantization_heisenbergEvolution
    (one : BoundedFreeSystem (EuclideanSpace ℂ Site))
    (many : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (hH : many.hamiltonian.1 = finiteSecondQuantization one.hamiltonian.1)
    (hhbar : many.hbar = one.hbar)
    (A : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site) (t : ℝ) :
    finiteSecondQuantization (heisenbergEvolution (freePropagatorGroup one) t A) =
      heisenbergEvolution (freePropagatorGroup many) t (finiteSecondQuantization A) := by
  have hgen : schrodingerGenerator many =
      finiteSecondQuantization (schrodingerGenerator one) := by
    simp only [schrodingerGenerator, hhbar, hH, map_smul]
  simp only [heisenbergEvolution_freePropagatorGroup_apply, freePropagator_eq_exp,
    hgen, ← RCLike.real_smul_eq_coe_smul (K := ℂ), neg_smul]
  simpa only [neg_smul, neg_neg] using
    finiteSecondQuantization_exp_conjugate (schrodingerGenerator one) A (-t)

/-- The full-Fock fixed-rate mixed susceptibility of a single-electron
state is the existing finite one-particle Lehmann table, for a supplied
energy eigenbasis with exactly one occupied level. The state on the
full Fock space is the normalized embedded eigenvector, not a separate
one-particle probability ansatz on the many-body space. -/
theorem adiabaticFrequencyDomainSusceptibility_oneParticleFock_eq_finiteLehmannTable
    {ι : Type*} [Fintype ι]
    (one : BoundedFreeSystem (EuclideanSpace ℂ Site))
    (many : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (hH : many.hamiltonian.1 = finiteSecondQuantization one.hamiltonian.1)
    (hhbar : many.hbar = one.hbar)
    (data : EnergyEigenbasisLehmannData one ι) (occupied : ι)
    (hoccupied : data.probability occupied = 1)
    (hzero : ∀ i, i ≠ occupied → data.probability i = 0)
    (A B : EuclideanSpace ℂ Site →L[ℂ] EuclideanSpace ℂ Site)
    (ω η : ℝ) (hη : 0 < η) :
    let ψ : StateVector (EuclideanSpace ℂ Site) :=
      ⟨data.basis occupied, data.basis.orthonormal.1 occupied⟩
    adiabaticFrequencyDomainSusceptibility (freePropagatorGroup many) many.hbar
      (QuantumTheory.pure (oneParticleFockState ψ)).toNormalizedExpectation
      (finiteSecondQuantization A) (finiteSecondQuantization B) ω η =
      finiteLehmannTableResponse one.hbar ω η (finiteLehmannTableOfEigenbasis one data A B) := by
  let ψ : StateVector (EuclideanSpace ℂ Site) :=
    ⟨data.basis occupied, data.basis.orthonormal.1 occupied⟩
  let ρ := (QuantumTheory.pure (oneParticleFockState ψ)).toNormalizedExpectation
  let U := freePropagatorGroup many
  let u := freePropagatorGroup one
  have hkernel (t : ℝ) :
      retardedTimeDifferenceKernel U many.hbar ρ
        (finiteSecondQuantization A) (finiteSecondQuantization B) t =
      retardedTimeDifferenceKernel u one.hbar
        (eigenbasisNormalizedExpectation one data) A B t := by
    by_cases ht : 0 ≤ t
    · rw [retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
        U many.hbar ρ _ _ ht,
        retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
          u one.hbar (eigenbasisNormalizedExpectation one data) A B ht]
      simp only [commutatorSusceptibility, heisenbergEvolution_zero, hhbar]
      rw [← finiteSecondQuantization_heisenbergEvolution one many hH hhbar A t,
        ← finiteSecondQuantization_lie]
      change (Complex.I / (one.hbar : ℂ)) *
          (QuantumTheory.pure (oneParticleFockState ψ)).toNormalizedExpectation
            (finiteSecondQuantization ⁅heisenbergEvolution u t A, B⁆) =
        (Complex.I / (one.hbar : ℂ)) *
          eigenbasisNormalizedExpectation one data ⁅heisenbergEvolution u t A, B⁆
      rw [DensityOperator.toNormalizedExpectation_apply, DensityOperator.expectation_pure,
        eigenbasisNormalizedExpectation_apply_of_single one data occupied hoccupied hzero]
      exact congrArg (fun z : ℂ => (Complex.I / (one.hbar : ℂ)) * z)
        (inner_finiteSecondQuantization_oneParticle
          ⁅heisenbergEvolution u t A, B⁆ (data.basis occupied) (data.basis occupied))
    · rw [retardedTimeDifferenceKernel_eq_zero_of_neg U many.hbar ρ _ _ (lt_of_not_ge ht),
        retardedTimeDifferenceKernel_eq_zero_of_neg u one.hbar
          (eigenbasisNormalizedExpectation one data) A B (lt_of_not_ge ht)]
  change adiabaticFrequencyDomainSusceptibility U many.hbar ρ
    (finiteSecondQuantization A) (finiteSecondQuantization B) ω η = _
  calc
    _ = adiabaticFrequencyDomainSusceptibility u one.hbar
        (eigenbasisNormalizedExpectation one data) A B ω η := by
          unfold adiabaticFrequencyDomainSusceptibility adiabaticFrequencySusceptibilityIntegrand
          simp_rw [hkernel]
    _ = _ := by
      rw [finiteLehmannTableResponse_ofEigenbasis]
      exact adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_lehmannSeries
        one data A B ω η hη (eigenbasisTimeDomainSummable_of_finite one data A B)

end
end SecondQuantization.Fermionic.Transport

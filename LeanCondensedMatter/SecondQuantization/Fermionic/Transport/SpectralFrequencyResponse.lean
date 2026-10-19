import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FrequencyResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.InfiniteTime
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.FrequencyDomain

set_option linter.style.header false

/-!
# Eigenbasis spectral form of the directional-current response

At fixed positive switching rate, the infinite-observation-time retarded directional coefficient
is the general adiabatic frequency-domain susceptibility of the continuity-derived current. The
existing eigenbasis Lehmann theorem therefore yields the finite double spectral sum directly. The
geometric Peierls contact expectation remains a separate explicit summand.

Diagonal transitions have zero current-current weight because their probability difference
vanishes. Equal-energy off-diagonal transitions are not silently discarded: unless their state
probabilities are also equal, they retain the regularized denominator `η - iω`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

open Set MeasureTheory QuantumTheory.LinearResponse

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

variable {ι : Type*}

/-- The full fixed-rate directional coefficient is the finite Lehmann sum plus the explicit
geometric Peierls contact expectation. -/
theorem infiniteTimeAdiabaticDirectionalResponse_eigenbasis_eq_finite_sum
    [Fintype ι]
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : EnergyEigenbasisLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    (boundedDirectionalResponseChannel system geometry direction K q).infiniteTimeAdiabaticResponse
        system (eigenbasisNormalizedExpectation system data) ω η =
      (∑ mn : ι × ι,
        (eigenbasisTransitionData system data
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K) mn).frequencyTerm ω η) +
        eigenbasisNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  unfold ResponseChannel.infiniteTimeAdiabaticResponse
  rw [infiniteTimeAdiabaticTransform_commutator_eq_susceptibility]
  rw [adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_finite_sum
    system data _ _ ω η hη]
  rfl

/-- The finite-time physical response converges directly to the finite Lehmann sum plus contact
term for a diagonal eigenbasis stationary state. -/
theorem hasInfiniteObservationTimeLimit_directional_eigenbasis_finite_sum
    [Fintype ι]
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : EnergyEigenbasisLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      ((boundedDirectionalResponseChannel system geometry direction K q).finiteTimeAdiabaticResponse
        system (eigenbasisNormalizedExpectation system data) ω η)
      ((∑ mn : ι × ι,
        (eigenbasisTransitionData system data
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K) mn).frequencyTerm ω η) +
        eigenbasisNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) := by
  have hlimit :=
    ResponseChannel.hasInfiniteObservationTimeLimit_finiteTimeAdiabaticResponse_of_stationary_pos
      (boundedDirectionalResponseChannel system geometry direction K q)
      system (eigenbasisNormalizedExpectation system data)
      (isStationary_eigenbasisNormalizedExpectation system data) ω η hη
  rw [infiniteTimeAdiabaticDirectionalResponse_eigenbasis_eq_finite_sum
    system data geometry direction K q ω η hη] at hlimit
  exact hlimit

end
end Transport
end Fermionic
end SecondQuantization

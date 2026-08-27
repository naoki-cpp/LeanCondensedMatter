import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.InfiniteTimeFrequencyResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.PurePointFrequencyDomain

set_option linter.style.header false

/-!
# Pure-point spectral form of the directional-current response

At fixed positive switching rate, the infinite-observation-time retarded directional coefficient
is the general adiabatic frequency-domain susceptibility of the continuity-derived current. The
existing pure-point Lehmann theorem therefore yields the finite double spectral sum directly. The
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

/-- The positive-lag field coefficient is exactly the general whole-line causal susceptibility. -/
theorem infiniteTimeAdiabaticDirectionalRetardedCoefficient_eq_susceptibility
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) :
    infiniteTimeAdiabaticDirectionalRetardedCoefficient
        system expectation geometry direction K q ω η =
      adiabaticFrequencyDomainSusceptibility system expectation
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K) ω η := by
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  change
    (∫ τ : ℝ in Ioi 0,
      adiabaticFrequencyPhase ω η τ *
        commutatorSusceptibility system expectation J J τ 0) =
      ∫ τ : ℝ,
        adiabaticFrequencySusceptibilityIntegrand
          system expectation J J ω η τ
  rw [integral_adiabaticFrequencySusceptibilityIntegrand_eq_Ioi_zero
    system expectation J J ω η]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ hτ
  have hτnonneg : 0 ≤ τ := le_of_lt hτ
  rw [adiabaticFrequencySusceptibilityIntegrand]
  rw [retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
    system expectation J J hτnonneg]

variable {ι : Type*}

/-- A diagonal current-current transition has zero Lehmann weight. -/
@[simp]
theorem purePointDirectionalCurrentTransitionWeight_diag
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) (i : ι) :
    purePointTransitionWeight system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K) (i, i) = 0 := by
  simp [purePointTransitionWeight]

/-- Equal-energy off-diagonal transitions retain the regularized denominator `η - iω`; their
weight is not assumed to vanish without an additional equality of state probabilities. -/
theorem purePointDirectionalCurrentLehmannTerm_of_equal_energy
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) {m n : ι}
    (henergy : data.energy m = data.energy n) :
    lehmannTerm system.hbar ω η
        (data.energy m - data.energy n)
        (purePointTransitionWeight system data
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K) (m, n)) =
      purePointTransitionWeight system data
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K) (m, n) *
        ((η : ℂ) - Complex.I * (ω : ℂ))⁻¹ := by
  have hgap : data.energy m - data.energy n = 0 := sub_eq_zero.mpr henergy
  rw [hgap]
  simp [lehmannTerm, lehmannDenominator]

/-- In a finite pure-point basis, the retarded directional coefficient is the conventional finite
double Lehmann sum at every `η > 0`. -/
theorem infiniteTimeAdiabaticDirectionalRetardedCoefficient_purePoint_eq_finite_sum
    [Fintype ι]
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    infiniteTimeAdiabaticDirectionalRetardedCoefficient
        system (purePointNormalizedExpectation system data)
        geometry direction K q ω η =
      ∑ mn : ι × ι,
        lehmannTerm system.hbar ω η
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K) mn) := by
  rw [infiniteTimeAdiabaticDirectionalRetardedCoefficient_eq_susceptibility]
  simpa [adiabaticFrequencyDomainSusceptibilityOfPositiveRate] using
    (adiabaticFrequencyDomainSusceptibilityOfPositiveRate_purePoint_eq_finite_sum
      system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K) ω η hη)

/-- The full fixed-rate directional coefficient is the finite Lehmann sum plus the explicit
geometric Peierls contact expectation. -/
theorem infiniteTimeAdiabaticDirectionalCoefficient_purePoint_eq_finite_sum
    [Fintype ι]
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    infiniteTimeAdiabaticDirectionalCoefficient
        system (purePointNormalizedExpectation system data)
        geometry direction K q ω η =
      (∑ mn : ι × ι,
        lehmannTerm system.hbar ω η
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K) mn)) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  rw [infiniteTimeAdiabaticDirectionalCoefficient]
  rw [infiniteTimeAdiabaticDirectionalRetardedCoefficient_purePoint_eq_finite_sum
    system data geometry direction K q ω η hη]

/-- The finite-time physical response converges directly to the finite Lehmann sum plus contact
term for a diagonal pure-point stationary state. -/
theorem hasInfiniteObservationTimeLimit_directional_purePoint_finite_sum
    [Fintype ι]
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalCoefficient
        system (purePointNormalizedExpectation system data)
          geometry direction K q ω η)
      ((∑ mn : ι × ι,
        lehmannTerm system.hbar ω η
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K) mn)) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) := by
  have hlimit := hasInfiniteObservationTimeLimit_directional_of_stationary_pos
    system (purePointNormalizedExpectation system data)
      (isStationary_purePointNormalizedExpectation system data)
      geometry direction K q ω η hη
  rw [infiniteTimeAdiabaticDirectionalCoefficient_purePoint_eq_finite_sum
    system data geometry direction K q ω η hη] at hlimit
  exact hlimit

end
end Transport
end Fermionic
end SecondQuantization

import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StationaryFrequencyResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticIntegrability
import LeanCondensedMatter.QuantumTheory.LinearResponse.InfiniteTimeAdiabatic

set_option linter.style.header false

/-!
# Fermionic infinite-observation-time adiabatic response

The representation-independent positive-lag integrability condition, half-infinite scalar adiabatic
transform, and finite-time `T → +∞` convergence theorem now live in
`QuantumTheory.LinearResponse.InfiniteTimeAdiabatic`.

This module retains the finite-lattice fermionic realization. For bounded directional currents, the
general linear-response integrability theorem supplies the generic scalar hypothesis whenever
`η > 0`; stationarity then identifies the finite-time directional response with the positive-lag
kernel before applying the generic observation-time limit. Frequency, switching, volume, and DC
limits remain separate and untaken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Integrability hypothesis specialized to the stationary directional-current lag kernel. -/
def StationaryDirectionalAdiabaticIntegrable
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : Prop :=
  AdiabaticLagIntegrable
    (stationaryDirectionalCurrentKernel
      system expectation geometry direction K q) ω η

/-- For bounded directional currents, every strictly positive switching rate supplies the required
positive-lag integrability automatically. -/
theorem stationaryDirectionalAdiabaticIntegrable_of_pos
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    StationaryDirectionalAdiabaticIntegrable
      system expectation geometry direction K q ω η := by
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  have hglobal :=
    QuantumTheory.LinearResponse.adiabaticIntegrable_of_pos
      system expectation J J ω η hη
  have hIoi : MeasureTheory.IntegrableOn
      (QuantumTheory.LinearResponse.adiabaticFrequencySusceptibilityIntegrand
        system expectation J J ω η)
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume :=
    hglobal.integrable.integrableOn
  unfold StationaryDirectionalAdiabaticIntegrable AdiabaticLagIntegrable
  apply hIoi.congr_fun
  · intro τ hτ
    have hτnonneg : 0 ≤ τ := le_of_lt hτ
    rw [QuantumTheory.LinearResponse.adiabaticFrequencySusceptibilityIntegrand]
    rw [QuantumTheory.LinearResponse.retardedTimeDifferenceKernel_eq_commutatorSusceptibility_of_nonneg
      system expectation J J hτnonneg]
    rfl
  · exact measurableSet_Ioi

/-- Infinite-observation-time retarded coefficient in a stationary state. -/
noncomputable def infiniteTimeAdiabaticDirectionalRetardedCoefficient
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : ℂ :=
  infiniteTimeAdiabaticTransform
    (stationaryDirectionalCurrentKernel
      system expectation geometry direction K q) ω η

/-- Infinite-observation-time total coefficient: retarded integral plus stationary contact term. -/
noncomputable def infiniteTimeAdiabaticDirectionalCoefficient
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : ℂ :=
  infiniteTimeAdiabaticDirectionalRetardedCoefficient
      system expectation geometry direction K q ω η +
    expectation
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)

/-- Under stationarity and weighted-lag integrability, the retarded directional coefficient has a
proved `T → +∞` limit at fixed `ω` and `η`. -/
theorem hasInfiniteObservationTimeLimit_directionalRetarded_of_stationary
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ)
    (hInt : StationaryDirectionalAdiabaticIntegrable
      system expectation geometry direction K q ω η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalRetardedCoefficient
        system expectation geometry direction K q ω η)
      (infiniteTimeAdiabaticDirectionalRetardedCoefficient
        system expectation geometry direction K q ω η) := by
  have h := hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform
    (stationaryDirectionalCurrentKernel
      system expectation geometry direction K q) ω η hInt
  unfold HasInfiniteObservationTimeLimit at h ⊢
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (finiteTimeAdiabaticDirectionalRetardedCoefficient_eq_stationaryLag
      system expectation hstationary geometry direction K q ω η hT).symm

/-- Under the same hypotheses, the full stationary coefficient including the contact response has
its `T → +∞` limit at fixed `ω` and `η`. -/
theorem hasInfiniteObservationTimeLimit_directional_of_stationary
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ)
    (hInt : StationaryDirectionalAdiabaticIntegrable
      system expectation geometry direction K q ω η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η)
      (infiniteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η) := by
  let C : ℂ := expectation
    (boundedDirectionalContact geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
  have h := hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform
    (stationaryDirectionalCurrentKernel
      system expectation geometry direction K q) ω η hInt
  unfold HasInfiniteObservationTimeLimit at h ⊢
  have hC : Filter.Tendsto (fun _ : ℝ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hsum := h.add hC
  have htotal : Filter.Tendsto
      (finiteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η)
      Filter.atTop
      (nhds
        (infiniteTimeAdiabaticTransform
            (stationaryDirectionalCurrentKernel
              system expectation geometry direction K q) ω η + C)) := by
    apply hsum.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    exact
      (finiteTimeAdiabaticDirectionalCoefficient_eq_stationaryLag
        system expectation hstationary geometry direction K q ω η hT).symm
  simpa [infiniteTimeAdiabaticDirectionalCoefficient,
    infiniteTimeAdiabaticDirectionalRetardedCoefficient, C] using htotal

/-- At every strictly positive switching rate, stationarity alone gives the retarded
observation-time limit. -/
theorem hasInfiniteObservationTimeLimit_directionalRetarded_of_stationary_pos
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalRetardedCoefficient
        system expectation geometry direction K q ω η)
      (infiniteTimeAdiabaticDirectionalRetardedCoefficient
        system expectation geometry direction K q ω η) :=
  hasInfiniteObservationTimeLimit_directionalRetarded_of_stationary
    system expectation hstationary geometry direction K q ω η
      (stationaryDirectionalAdiabaticIntegrable_of_pos
        system expectation geometry direction K q ω η hη)

/-- At every strictly positive switching rate, stationarity alone gives the full observation-time
limit including the Peierls contact response. -/
theorem hasInfiniteObservationTimeLimit_directional_of_stationary_pos
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η)
      (infiniteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η) :=
  hasInfiniteObservationTimeLimit_directional_of_stationary
    system expectation hstationary geometry direction K q ω η
      (stationaryDirectionalAdiabaticIntegrable_of_pos
        system expectation geometry direction K q ω η hη)

end
end Transport
end Fermionic
end SecondQuantization

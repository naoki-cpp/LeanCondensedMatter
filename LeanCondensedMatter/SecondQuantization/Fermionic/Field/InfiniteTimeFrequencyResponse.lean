import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StationaryFrequencyResponse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.style.header false

/-!
# Infinite-observation-time adiabatic response

The stationary finite-time response is an interval integral over the positive lag variable. This
module takes the first regulator limit under an explicit Bochner-integrability hypothesis:

```text
∫₀ᵀ dτ exp ((-η + iω) τ) K(τ)
  ⟶ ∫_(0,∞) dτ exp ((-η + iω) τ) K(τ)
```

as `T → +∞`. The switching rate and driving frequency remain fixed. No zero-switching,
thermodynamic, or DC limit is taken or inferred.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

/-- Explicit integrability hypothesis for the adiabatically weighted positive-lag kernel. -/
def AdiabaticLagIntegrable (kernel : ℝ → ℂ) (ω η : ℝ) : Prop :=
  MeasureTheory.IntegrableOn
    (fun τ => adiabaticFrequencyFactor ω η τ * kernel τ)
    (Set.Ioi (0 : ℝ)) MeasureTheory.volume

/-- The half-infinite adiabatic transform at fixed frequency and switching rate. -/
noncomputable def infiniteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η : ℝ) : ℂ :=
  ∫ τ in Set.Ioi (0 : ℝ), adiabaticFrequencyFactor ω η τ * kernel τ

/-- Integrability of the weighted lag kernel is sufficient for the observation-time limit. -/
theorem hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform
    (kernel : ℝ → ℂ) (ω η : ℝ)
    (hInt : AdiabaticLagIntegrable kernel ω η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticTransform kernel ω η)
      (infiniteTimeAdiabaticTransform kernel ω η) := by
  unfold HasInfiniteObservationTimeLimit
  simpa only [finiteTimeAdiabaticTransform, infiniteTimeAdiabaticTransform] using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := MeasureTheory.volume)
      (f := fun τ : ℝ => adiabaticFrequencyFactor ω η τ * kernel τ)
      (b := fun T : ℝ => T) (0 : ℝ) hInt tendsto_id)

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
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
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
  have h := hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform
    (stationaryDirectionalCurrentKernel
      system expectation geometry direction K q) ω η hInt
  unfold HasInfiniteObservationTimeLimit at h ⊢
  have hsum := h.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (finiteTimeAdiabaticDirectionalCoefficient_eq_stationaryLag
      system expectation hstationary geometry direction K q ω η hT).symm

end
end Field
end Fermionic
end SecondQuantization

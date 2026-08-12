import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.HarmonicSourceResponse

set_option linter.style.header false

/-!
# Stationary lag representation of the finite-frequency response

For a stationary expectation, the two-time retarded current kernel depends only on the lag
`τ = T - s`. On a nonnegative observation interval, the finite-time adiabatic coefficient can
therefore be rewritten exactly as an integral over positive lags:

```text
∫₀ᵀ ds exp ((-η + iω) (T-s)) χᴿ(T,s)
  = ∫₀ᵀ dτ exp ((-η + iω) τ) χ(τ,0).
```

This is only a change of representation at finite `T`. No infinite-time, zero-switching, or DC
limit is taken. The contact expectation is also time independent under the same stationarity
hypothesis.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Lattice

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- One-lag directional-current commutator kernel in a stationary state. Causality is supplied by
integrating only over nonnegative lags. -/
noncomputable def stationaryDirectionalCurrentKernel
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q τ : ℝ) : ℂ :=
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  QuantumTheory.LinearResponse.commutatorSusceptibility
    system expectation J J τ 0

/-- Stationarity turns the finite-time two-time retarded coefficient into the scalar adiabatic
transform of the one-lag current kernel. -/
theorem finiteTimeAdiabaticDirectionalRetardedCoefficient_eq_stationaryLag
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    finiteTimeAdiabaticDirectionalRetardedCoefficient
        system expectation geometry direction K q ω η T =
      finiteTimeAdiabaticTransform
        (stationaryDirectionalCurrentKernel
          system expectation geometry direction K q) ω η T := by
  let J := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  let g : ℝ → ℂ := fun τ =>
    adiabaticFrequencyFactor ω η τ *
      QuantumTheory.LinearResponse.commutatorSusceptibility
        system expectation J J τ 0
  change
    (∫ s in (0 : ℝ)..T,
      adiabaticFrequencyFactor ω η (T - s) *
        QuantumTheory.LinearResponse.retardedSusceptibility
          system expectation J J T s) =
      ∫ τ in (0 : ℝ)..T, g τ
  calc
    _ = ∫ s in (0 : ℝ)..T, g (T - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
        simpa [Set.uIcc_of_le hT] using hs
      change
        adiabaticFrequencyFactor ω η (T - s) *
            QuantumTheory.LinearResponse.retardedSusceptibility
              system expectation J J T s =
          g (T - s)
      rw [QuantumTheory.LinearResponse.retardedSusceptibility_eq_timeDifference_of_stationary
        system expectation hstationary J J T s]
      simp [g, sub_nonneg.mpr hsIcc.2]
    _ = ∫ τ in (0 : ℝ)..T, g τ := by
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := T) g T)

/-- In a stationary state, the evolved directional contact has the same expectation as the
unevolved contact operator. -/
theorem boundedDirectionalContactExpectation_eq_of_stationary
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q T : ℝ) :
    boundedDirectionalContactExpectation
        system expectation geometry direction K q T =
      expectation
        (boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K) := by
  exact hstationary T
    (boundedDirectionalContact geometry direction
      (system.hbar : ℂ) (q : ℂ) K)

/-- Exact stationary finite-time coefficient: a positive-lag transform plus the unevolved contact
expectation. This remains a finite-volume, finite-`T`, finite-`η` identity. -/
theorem finiteTimeAdiabaticDirectionalCoefficient_eq_stationaryLag
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (hstationary : QuantumTheory.LinearResponse.IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    finiteTimeAdiabaticDirectionalCoefficient
        system expectation geometry direction K q ω η T =
      finiteTimeAdiabaticTransform
          (stationaryDirectionalCurrentKernel
            system expectation geometry direction K q) ω η T +
        expectation
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  rw [finiteTimeAdiabaticDirectionalCoefficient_eq]
  rw [finiteTimeAdiabaticDirectionalRetardedCoefficient_eq_stationaryLag
    system expectation hstationary geometry direction K q ω η hT]
  rw [boundedDirectionalContactExpectation_eq_of_stationary
    system expectation hstationary geometry direction K q T]

end
end Transport
end Fermionic
end SecondQuantization

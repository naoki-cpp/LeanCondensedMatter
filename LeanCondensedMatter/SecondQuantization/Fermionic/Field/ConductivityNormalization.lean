import LeanCondensedMatter.Transport.FiniteVolume
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SpectralFrequencyResponse

set_option linter.style.header false

/-!
# Finite-volume electric-field conductivity convention

The directional coefficient constructed upstream is the response of the total directional current
to a uniform Peierls vector-potential amplitude. For the source convention

```text
A(t) ∝ exp (η t) exp (-i ω t),
```

the corresponding complex electric-field amplitude is

```text
E(t) = -∂ₜ A(t) = (-η + iω) A(t).
```

This module makes the remaining normalization explicit. Canonical positive finite-volume data are
supplied by `QuantumTheory.Transport.PositiveVolume`; dividing the total-current response by that
volume gives current density, and dividing by `-η + iω` converts vector-potential response to
electric-field response. The resulting object is called conductivity only with this convention
visible.

The first slice is finite volume, uses the full finite fermionic Fock space, and couples a single
uniform directional Peierls source to the finite hopping model. Boundary conditions and geometry
are encoded by the finite site type, hopping amplitudes, and `LatticeGeometry`; no infinite-volume
trace per unit volume or equivalence of electromagnetic gauges is claimed. The limits `η → 0⁺`
and `ω → 0` remain separate and untaken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open QuantumTheory.LinearResponse

noncomputable section

/-- For `A(t) ∝ exp (ηt) exp (-iωt)`, the electric-field amplitude is
`(-η + iω) A(t)`. -/
def adiabaticElectricFieldFactor (ω η : ℝ) : ℂ :=
  -(η : ℂ) + Complex.I * (ω : ℂ)

@[simp]
theorem adiabaticElectricFieldFactor_re (ω η : ℝ) :
    (adiabaticElectricFieldFactor ω η).re = -η := by
  simp [adiabaticElectricFieldFactor]

@[simp]
theorem adiabaticElectricFieldFactor_im (ω η : ℝ) :
    (adiabaticElectricFieldFactor ω η).im = ω := by
  simp [adiabaticElectricFieldFactor]

@[simp]
theorem adiabaticElectricFieldFactor_zero_frequency (η : ℝ) :
    adiabaticElectricFieldFactor 0 η = -(η : ℂ) := by
  simp [adiabaticElectricFieldFactor]

@[simp]
theorem adiabaticElectricFieldFactor_zero_switching (ω : ℝ) :
    adiabaticElectricFieldFactor ω 0 = Complex.I * (ω : ℂ) := by
  simp [adiabaticElectricFieldFactor]

/-- A strictly positive switching rate keeps the electric-field conversion factor nonzero, even at
zero driving frequency. -/
theorem adiabaticElectricFieldFactor_ne_zero_of_pos
    (ω η : ℝ) (hη : 0 < η) :
    adiabaticElectricFieldFactor ω η ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [adiabaticElectricFieldFactor] at hre
  linarith

/-- Combined conversion from total-current/vector-potential response to
current-density/electric-field response. -/
noncomputable def finiteVolumeConductivityNormalization
    (volume : QuantumTheory.Transport.PositiveVolume) (ω η : ℝ) : ℂ :=
  (((volume.volume : ℂ) * adiabaticElectricFieldFactor ω η))⁻¹

/-- The finite-volume normalization denominator is nonzero at every positive switching rate. -/
theorem finiteVolumeConductivityDenominator_ne_zero
    (volume : QuantumTheory.Transport.PositiveVolume)
    (ω η : ℝ) (hη : 0 < η) :
    (volume.volume : ℂ) * adiabaticElectricFieldFactor ω η ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt volume.volume_pos
  · exact adiabaticElectricFieldFactor_ne_zero_of_pos ω η hη

/-- Convert a total-current response coefficient with respect to vector potential into an
intensive electric-field conductivity. -/
noncomputable def finiteVolumeConductivityFromVectorPotential
    (volume : QuantumTheory.Transport.PositiveVolume)
    (ω η : ℝ) (response : ℂ) : ℂ :=
  response * finiteVolumeConductivityNormalization volume ω η

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Finite-observation-time, finite-volume regularized conductivity. -/
noncomputable def finiteTimeAdiabaticDirectionalConductivity
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  finiteVolumeConductivityFromVectorPotential volume ω η
    (finiteTimeAdiabaticDirectionalCoefficient
      system expectation geometry direction K q ω η T)

/-- Infinite-observation-time, finite-volume regularized conductivity at fixed `ω` and `η`. -/
noncomputable def infiniteTimeAdiabaticDirectionalConductivity
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : ℂ :=
  finiteVolumeConductivityFromVectorPotential volume ω η
    (infiniteTimeAdiabaticDirectionalCoefficient
      system expectation geometry direction K q ω η)

/-- Stationarity and `η > 0` give the observation-time limit for the explicitly normalized
finite-volume conductivity. -/
theorem hasInfiniteObservationTimeLimit_directionalConductivity_of_stationary_pos
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (hstationary : IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalConductivity volume
        system expectation geometry direction K q ω η)
      (infiniteTimeAdiabaticDirectionalConductivity volume
        system expectation geometry direction K q ω η) := by
  have hlimit := hasInfiniteObservationTimeLimit_directional_of_stationary_pos
    system expectation hstationary geometry direction K q ω η hη
  unfold HasInfiniteObservationTimeLimit at hlimit ⊢
  change Filter.Tendsto
    (fun T : ℝ =>
      finiteTimeAdiabaticDirectionalCoefficient
          system expectation geometry direction K q ω η T *
        finiteVolumeConductivityNormalization volume ω η)
    Filter.atTop
    (nhds
      (infiniteTimeAdiabaticDirectionalCoefficient
          system expectation geometry direction K q ω η *
        finiteVolumeConductivityNormalization volume ω η))
  exact hlimit.mul
    (tendsto_const_nhds :
      Filter.Tendsto
        (fun _ : ℝ => finiteVolumeConductivityNormalization volume ω η)
        Filter.atTop
        (nhds (finiteVolumeConductivityNormalization volume ω η)))

variable {ι : Type*}

/-- The finite pure-point conductivity is the Lehmann current response plus contact response,
multiplied by the explicit volume and electric-field normalization. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_purePoint_eq_finite_sum
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    infiniteTimeAdiabaticDirectionalConductivity volume
        system (purePointNormalizedExpectation system data)
          geometry direction K q ω η =
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
            (system.hbar : ℂ) (q : ℂ) K)) *
        finiteVolumeConductivityNormalization volume ω η := by
  rw [infiniteTimeAdiabaticDirectionalConductivity]
  rw [finiteVolumeConductivityFromVectorPotential]
  rw [infiniteTimeAdiabaticDirectionalCoefficient_purePoint_eq_finite_sum
    system data geometry direction K q ω η hη]

/-- The finite-time conductivity converges directly to the normalized finite Lehmann sum plus
contact term. -/
theorem hasInfiniteObservationTimeLimit_directionalConductivity_purePoint_finite_sum
    [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalConductivity volume
        system (purePointNormalizedExpectation system data)
          geometry direction K q ω η)
      (((∑ mn : ι × ι,
        lehmannTerm system.hbar ω η
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K) mn)) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) *
        finiteVolumeConductivityNormalization volume ω η) := by
  have hlimit := hasInfiniteObservationTimeLimit_directionalConductivity_of_stationary_pos
    volume system (purePointNormalizedExpectation system data)
      (isStationary_purePointNormalizedExpectation system data)
      geometry direction K q ω η hη
  rw [infiniteTimeAdiabaticDirectionalConductivity_purePoint_eq_finite_sum
    volume system data geometry direction K q ω η hη] at hlimit
  exact hlimit

end
end Field
end Fermionic
end SecondQuantization

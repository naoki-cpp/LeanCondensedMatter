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

This module makes the remaining normalization explicit. A positive finite volume is supplied as
data; dividing the total-current response by that volume gives current density, and dividing by
`-η + iω` converts vector-potential response to electric-field response. The resulting object is
called conductivity only with this convention visible.

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

/-- Positive finite volume used to convert the total directional current into current density. -/
structure FiniteVolumeConductivityConvention where
  volume : ℝ
  volume_pos : 0 < volume

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
    (convention : FiniteVolumeConductivityConvention) (ω η : ℝ) : ℂ :=
  (((convention.volume : ℂ) * adiabaticElectricFieldFactor ω η))⁻¹

/-- The finite-volume normalization denominator is nonzero at every positive switching rate. -/
theorem finiteVolumeConductivityDenominator_ne_zero
    (convention : FiniteVolumeConductivityConvention)
    (ω η : ℝ) (hη : 0 < η) :
    (convention.volume : ℂ) * adiabaticElectricFieldFactor ω η ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt convention.volume_pos
  · exact adiabaticElectricFieldFactor_ne_zero_of_pos ω η hη

/-- Convert a total-current response coefficient with respect to vector potential into an
intensive electric-field conductivity. -/
noncomputable def finiteVolumeConductivityFromVectorPotential
    (convention : FiniteVolumeConductivityConvention)
    (ω η : ℝ) (response : ℂ) : ℂ :=
  response * finiteVolumeConductivityNormalization convention ω η

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Finite-observation-time, finite-volume regularized conductivity. -/
noncomputable def finiteTimeAdiabaticDirectionalConductivity
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η T : ℝ) : ℂ :=
  finiteVolumeConductivityFromVectorPotential convention ω η
    (finiteTimeAdiabaticDirectionalCoefficient
      system expectation geometry direction K q ω η T)

/-- Infinite-observation-time, finite-volume regularized conductivity at fixed `ω` and `η`. -/
noncomputable def infiniteTimeAdiabaticDirectionalConductivity
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) : ℂ :=
  finiteVolumeConductivityFromVectorPotential convention ω η
    (infiniteTimeAdiabaticDirectionalCoefficient
      system expectation geometry direction K q ω η)

/-- Stationarity and `η > 0` give the observation-time limit for the explicitly normalized
finite-volume conductivity. -/
theorem hasInfiniteObservationTimeLimit_directionalConductivity_of_stationary_pos
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock Site))
    (hstationary : IsStationary system expectation)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalConductivity convention
        system expectation geometry direction K q ω η)
      (infiniteTimeAdiabaticDirectionalConductivity convention
        system expectation geometry direction K q ω η) := by
  have hlimit := hasInfiniteObservationTimeLimit_directional_of_stationary_pos
    system expectation hstationary geometry direction K q ω η hη
  unfold HasInfiniteObservationTimeLimit at hlimit ⊢
  let c : ℂ := finiteVolumeConductivityNormalization convention ω η
  have hc : Filter.Tendsto (fun _ : ℝ => c) Filter.atTop (nhds c) :=
    tendsto_const_nhds
  have hmul := hlimit.mul hc
  simpa [finiteTimeAdiabaticDirectionalConductivity,
    infiniteTimeAdiabaticDirectionalConductivity,
    finiteVolumeConductivityFromVectorPotential, c] using hmul

variable {ι : Type*}

/-- The finite pure-point conductivity is the Lehmann current response plus contact response,
multiplied by the explicit volume and electric-field normalization. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_purePoint_eq_finite_sum
    [Fintype ι]
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    infiniteTimeAdiabaticDirectionalConductivity convention
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
        finiteVolumeConductivityNormalization convention ω η := by
  rw [infiniteTimeAdiabaticDirectionalConductivity]
  rw [finiteVolumeConductivityFromVectorPotential]
  rw [infiniteTimeAdiabaticDirectionalCoefficient_purePoint_eq_finite_sum
    system data geometry direction K q ω η hη]

/-- The finite-time conductivity converges directly to the normalized finite Lehmann sum plus
contact term. -/
theorem hasInfiniteObservationTimeLimit_directionalConductivity_purePoint_finite_sum
    [Fintype ι]
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q ω η : ℝ) (hη : 0 < η) :
    HasInfiniteObservationTimeLimit
      (finiteTimeAdiabaticDirectionalConductivity convention
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
        finiteVolumeConductivityNormalization convention ω η) := by
  have hlimit := hasInfiniteObservationTimeLimit_directionalConductivity_of_stationary_pos
    convention system (purePointNormalizedExpectation system data)
      (isStationary_purePointNormalizedExpectation system data)
      geometry direction K q ω η hη
  rw [infiniteTimeAdiabaticDirectionalConductivity_purePoint_eq_finite_sum
    convention system data geometry direction K q ω η hη] at hlimit
  exact hlimit

end
end Field
end Fermionic
end SecondQuantization

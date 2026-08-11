import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaOccupation

set_option linter.style.header false

/-!
# Common energy kernel for finite Kubo–Bastin response

Finite transition intervals are localized on the full energy axis and summed into one integrable
piecewise kernel. This kernel is generally discontinuous at spectral energies, so it is not yet the
smooth Středa primitive required for the surface/sea integration-by-parts theorem.
-/

namespace SecondQuantization.Fermionic.Field

open MeasureTheory QuantumTheory.LinearResponse Set

noncomputable section

/-- A full-line function encoding the oriented interval integral from `a` to `b`. -/
noncomputable def orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b energy : ℝ) : ℂ :=
  (Ioc a b).indicator f energy - (Ioc b a).indicator f energy

theorem integrable_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    Integrable (orientedIntervalIntegrand f a b) := by
  unfold orientedIntervalIntegrand
  exact (hf.1.integrable_indicator measurableSet_Ioc).sub
    (hf.2.integrable_indicator measurableSet_Ioc)

theorem integral_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    (∫ energy : ℝ, orientedIntervalIntegrand f a b energy) =
      ∫ energy in a..b, f energy := by
  unfold orientedIntervalIntegrand
  rw [MeasureTheory.integral_sub
    (hf.1.integrable_indicator measurableSet_Ioc)
    (hf.2.integrable_indicator measurableSet_Ioc)]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc]
  rfl

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- The full-line localized integrand associated with one finite Bastin transition. -/
noncomputable def finiteKuboBastinCommonTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) (energy : ℝ) : ℂ :=
  orientedIntervalIntegrand
    ((-finiteKuboBastinDirectionalTransitionFactor
      system data geometry direction K q omega eta mn) •
      interpolation.occupationDerivative)
    (data.energy mn.2) (data.energy mn.1) energy

theorem integrable_finiteKuboBastinCommonTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (mn : ι × ι) :
    Integrable (finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn) := by
  apply integrable_orientedIntervalIntegrand
  exact (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul
    (-finiteKuboBastinDirectionalTransitionFactor
      system data geometry direction K q omega eta mn)

theorem integral_finiteKuboBastinCommonTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (mn : ι × ι) :
    (∫ energy : ℝ, finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn energy) =
      finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
        system data interpolation geometry direction K q omega eta mn := by
  let factor := finiteKuboBastinDirectionalTransitionFactor
    system data geometry direction K q omega eta mn
  have hint : IntervalIntegrable ((-factor) • interpolation.occupationDerivative)
      volume (data.energy mn.2) (data.energy mn.1) :=
    (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul (-factor)
  rw [show finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn =
      orientedIntervalIntegrand ((-factor) • interpolation.occupationDerivative)
        (data.energy mn.2) (data.energy mn.1) by rfl]
  rw [integral_orientedIntervalIntegrand _ _ _ hint]
  change (∫ energy in data.energy mn.2..data.energy mn.1,
      (-factor) • interpolation.occupationDerivative energy) = _
  rw [intervalIntegral.integral_smul]
  unfold finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
  simp only [smul_eq_mul]
  ring

variable [Fintype ι]

/-- The finite sum of all localized transition integrands on the full energy axis. -/
noncomputable def finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι, finiteKuboBastinCommonTransitionIntegrand
    system data interpolation geometry direction K q omega eta mn energy

theorem integrable_finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    Integrable (finiteKuboBastinCommonEnergyKernel
      system data interpolation geometry direction K q omega eta) := by
  unfold finiteKuboBastinCommonEnergyKernel
  apply integrable_finsetSum
  intro mn _
  exact integrable_finiteKuboBastinCommonTransitionIntegrand
    system data interpolation geometry direction K q omega eta mn

theorem integral_finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    (∫ energy : ℝ, finiteKuboBastinCommonEnergyKernel
      system data interpolation geometry direction K q omega eta energy) =
      ∑ mn : ι × ι, finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
        system data interpolation geometry direction K q omega eta mn := by
  unfold finiteKuboBastinCommonEnergyKernel
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro mn _
    exact integral_finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn
  · intro mn _
    exact integrable_finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn

/-- The common-energy-kernel conductivity with contact and finite-volume normalization. -/
noncomputable def finiteKuboBastinCommonEnergyDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℂ :=
  ((∫ energy : ℝ, finiteKuboBastinCommonEnergyKernel
      system data interpolation geometry direction K q omega eta energy) +
    purePointNormalizedExpectation system data
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization convention omega eta

theorem finiteKuboBastinOccupationResolvedDirectionalConductivity_eq_commonEnergy
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta =
      finiteKuboBastinCommonEnergyDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta := by
  unfold finiteKuboBastinOccupationResolvedDirectionalConductivity
    finiteKuboBastinCommonEnergyDirectionalConductivity
  rw [integral_finiteKuboBastinCommonEnergyKernel]

theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_commonEnergy
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinCommonEnergyDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta := by
  calc
    _ = finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteDimensionalKuboBastinDirectionalConductivity_eq_occupationResolved
        convention system data interpolation geometry direction K q omega eta
    _ = _ := finiteKuboBastinOccupationResolvedDirectionalConductivity_eq_commonEnergy
      convention system data interpolation geometry direction K q omega eta

end

end SecondQuantization.Fermionic.Field

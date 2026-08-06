import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaOccupation

set_option linter.style.header false

/-!
# A common full-energy kernel for the finite regularized Bastin response

The occupation bridge rewrites each pure-point transition using its own oriented interval
`Eₙ..Eₘ`. This module combines those finitely many transition integrals into one Bochner integral
over the full real energy axis.

For a function `g`, define its oriented interval localization by

```text
1_(a,b] g - 1_(b,a] g.
```

Its full-line integral is exactly the interval integral `∫_[a,b] g`. Summing these localized
transition integrands therefore produces a single piecewise common energy kernel whose integral is
the complete current-current part of the finite Kubo–Bastin response.

The resulting kernel is generally discontinuous at the discrete energy eigenvalues. Consequently
it is not silently identified with the differentiable `surfacePrimitive` required by
`StredaIntegration`. Constructing a smooth resolvent-based Bastin primitive and its residual sea
kernel remains the next layer. No zero-temperature distributional derivative, zero-broadening, DC,
disorder, trace-per-volume, or thermodynamic-limit claim is made.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open MeasureTheory QuantumTheory.LinearResponse Set

noncomputable section

/-- A function localized to the oriented interval from `a` to `b`. -/
noncomputable def orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b energy : ℝ) : ℂ :=
  (Ioc a b).indicator f energy - (Ioc b a).indicator f energy

/-- Interval integrability is exactly enough to make the oriented localization globally
integrable. -/
theorem integrable_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    Integrable (orientedIntervalIntegrand f a b) := by
  unfold orientedIntervalIntegrand
  exact (hf.1.integrable_indicator measurableSet_Ioc).sub
    (hf.2.integrable_indicator measurableSet_Ioc)

/-- The full-line integral of the oriented localization is the corresponding interval integral. -/
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
variable [Fintype ι]

/-- The globally defined energy integrand associated with one finite Bastin transition. -/
noncomputable def finiteKuboBastinCommonTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) (energy : ℝ) : ℂ :=
  orientedIntervalIntegrand
    (fun x =>
      (-finiteKuboBastinDirectionalTransitionFactor
        system data geometry direction K q omega eta mn) *
        interpolation.occupationDerivative x)
    (data.energy mn.2) (data.energy mn.1) energy

/-- Every localized finite-transition integrand is globally integrable. -/
theorem integrable_finiteKuboBastinCommonTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    Integrable (finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn) := by
  apply integrable_orientedIntervalIntegrand
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul
      (-finiteKuboBastinDirectionalTransitionFactor
        system data geometry direction K q omega eta mn)

/-- Integrating one globally localized transition gives its occupation-resolved finite Bastin
term. -/
theorem integral_finiteKuboBastinCommonTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    (∫ energy : ℝ,
      finiteKuboBastinCommonTransitionIntegrand
        system data interpolation geometry direction K q omega eta mn energy) =
      finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
        system data interpolation geometry direction K q omega eta mn := by
  let factor := finiteKuboBastinDirectionalTransitionFactor
    system data geometry direction K q omega eta mn
  have hint : IntervalIntegrable
      (fun x => (-factor) * interpolation.occupationDerivative x)
      volume (data.energy mn.2) (data.energy mn.1) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul (-factor)
  rw [show finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn =
      orientedIntervalIntegrand
        (fun x => (-factor) * interpolation.occupationDerivative x)
        (data.energy mn.2) (data.energy mn.1) by rfl]
  rw [integral_orientedIntervalIntegrand _ _ _ hint]
  rw [intervalIntegral.integral_const_mul]
  unfold finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
  change (-factor) *
      (∫ energy in data.energy mn.2..data.energy mn.1,
        interpolation.occupationDerivative energy) = _
  ring

/-- The single piecewise full-energy kernel obtained by summing all finite spectral transitions. -/
noncomputable def finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι,
    finiteKuboBastinCommonTransitionIntegrand
      system data interpolation geometry direction K q omega eta mn energy

/-- The finite common energy kernel is globally integrable. -/
theorem integrable_finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    Integrable (finiteKuboBastinCommonEnergyKernel
      system data interpolation geometry direction K q omega eta) := by
  unfold finiteKuboBastinCommonEnergyKernel
  apply integrable_finset_sum
  intro mn _
  exact integrable_finiteKuboBastinCommonTransitionIntegrand
    system data interpolation geometry direction K q omega eta mn

/-- The full-line integral of the common kernel is exactly the finite current-current transition
sum. -/
theorem integral_finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    (∫ energy : ℝ,
      finiteKuboBastinCommonEnergyKernel
        system data interpolation geometry direction K q omega eta energy) =
      ∑ mn : ι × ι,
        finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
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

/-- The finite conductivity written with one common full-energy kernel, plus the unchanged contact
term and finite-volume electric-field normalization. -/
noncomputable def finiteKuboBastinCommonEnergyDirectionalConductivity
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℂ :=
  ((∫ energy : ℝ,
      finiteKuboBastinCommonEnergyKernel
        system data interpolation geometry direction K q omega eta energy) +
      purePointNormalizedExpectation system data
        (boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization convention omega eta

/-- The occupation-resolved finite conductivity equals the single common-energy-kernel form. -/
theorem finiteKuboBastinOccupationResolvedDirectionalConductivity_eq_commonEnergy
    (convention : FiniteVolumeConductivityConvention)
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

/-- The ordinary-trace finite Kubo–Bastin response therefore has one explicit full-energy kernel. -/
theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_commonEnergy
    (convention : FiniteVolumeConductivityConvention)
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
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteDimensionalKuboBastinDirectionalConductivity_eq_occupationResolved
        convention system data interpolation geometry direction K q omega eta
    _ = finiteKuboBastinCommonEnergyDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteKuboBastinOccupationResolvedDirectionalConductivity_eq_commonEnergy
        convention system data interpolation geometry direction K q omega eta

end
end Field
end Fermionic
end SecondQuantization

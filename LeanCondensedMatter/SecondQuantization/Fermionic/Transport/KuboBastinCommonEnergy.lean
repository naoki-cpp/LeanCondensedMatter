import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinOccupation
import LeanCondensedMatter.Transport.KuboBastin.CommonEnergy

set_option linter.style.header false

/-!
# Fermionic directional common-energy Kubo–Bastin kernel

The statistics-independent common-energy construction now lives in
`QuantumTheory.Transport.KuboBastin.CommonEnergy`. This module retains only the finite-lattice
directional charge-current specialization, including the Peierls contact and finite-volume
conductivity normalization.

The common kernel remains a finite full-energy representation at fixed broadening. No canonical
smooth Středa representation, zero-broadening/DC limit, disorder, trace-per-volume, or
thermodynamic-limit claim is made here.
-/

namespace SecondQuantization.Fermionic.Transport

open SecondQuantization.Fermionic.Lattice
open MeasureTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site ι E : Type*}
variable [Fintype Site] [Fintype ι]
variable [LinearOrder Site]
variable [AddCommGroup E] [Module ℝ E]

/-- The full-line localized integrand associated with one finite directional Bastin transition. -/
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

omit [Fintype ι] in
theorem finiteKuboBastinCommonTransitionIntegrand_eq_vertex
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    finiteKuboBastinCommonTransitionIntegrand
        system data interpolation geometry direction K q omega eta mn =
      purePointKuboBastinCommonVertexTransitionIntegrand system data interpolation
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        omega eta mn := by
  rfl

omit [Fintype ι] in
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

omit [Fintype ι] in
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
  rw [finiteKuboBastinCommonTransitionIntegrand_eq_vertex
    system data interpolation geometry direction K q omega eta mn]
  rw [integral_purePointKuboBastinCommonVertexTransitionIntegrand]
  exact (finiteKuboBastinOccupationResolvedDirectionalCurrentTerm_eq_vertex
    system data interpolation geometry direction K q omega eta mn).symm

/-- The finite sum of all localized directional transition integrands on the full energy axis. -/
noncomputable def finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι, finiteKuboBastinCommonTransitionIntegrand
    system data interpolation geometry direction K q omega eta mn energy

theorem finiteKuboBastinCommonEnergyKernel_eq_vertex
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteKuboBastinCommonEnergyKernel
        system data interpolation geometry direction K q omega eta =
      finiteKuboBastinCommonVertexEnergyKernel system data interpolation
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        omega eta := by
  funext energy
  rfl

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
  rw [finiteKuboBastinOccupationResolvedVertexResponse_eq_commonEnergy
    system data interpolation
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalContact geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta]
  unfold finiteKuboBastinCommonEnergyVertexResponse
  rw [← finiteKuboBastinCommonEnergyKernel_eq_vertex
    system data interpolation geometry direction K q omega eta]

/-- The finite spectral conductivity equals its common-energy representation, without introducing
an artificial ordinary-trace carrier. -/
theorem finiteKuboBastinSpectralDirectionalConductivity_eq_commonEnergy
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention =
      finiteKuboBastinCommonEnergyDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta := by
  calc
    _ = finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteKuboBastinSpectralDirectionalConductivity_eq_occupationResolved
        convention system data interpolation geometry direction K q omega eta
    _ = _ := finiteKuboBastinOccupationResolvedDirectionalConductivity_eq_commonEnergy
      convention system data interpolation geometry direction K q omega eta

end

end SecondQuantization.Fermionic.Transport

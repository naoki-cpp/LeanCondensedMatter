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

/-- The finite directional common-energy kernel, obtained by specializing the generic
measured/source vertex kernel to the bounded directional current. -/
noncomputable def finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℝ → ℂ :=
  finiteKuboBastinCommonVertexEnergyKernel system data interpolation
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta

theorem integrable_finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    Integrable (finiteKuboBastinCommonEnergyKernel
      system data interpolation geometry direction K q omega eta) := by
  simpa [finiteKuboBastinCommonEnergyKernel] using
    (integrable_finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta)

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
  simpa [finiteKuboBastinCommonEnergyKernel,
    finiteKuboBastinOccupationResolvedDirectionalCurrentTerm] using
    (integral_finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta)

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
    _ = _ := by
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
      rfl

end

end SecondQuantization.Fermionic.Transport

import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral
import LeanCondensedMatter.Transport.KuboBastin.Occupation

set_option linter.style.header false

/-!
# Fermionic directional occupation-resolved Kubo–Bastin response

The statistics-independent occupation interpolation and arbitrary measured/source Kubo–Bastin
response now live under `QuantumTheory.Transport`, in `KuboBastin.OccupationInterpolation` and
`KuboBastin.Occupation`. This module retains only the finite-lattice directional charge-current
specialization with its Peierls contact and finite-volume normalization.

For each directional transition the discrete probability difference is replaced by the oriented
energy integral of the supplied occupation derivative. The resulting response remains connected
to the causal Kubo / spectral Kubo–Bastin chain at fixed positive switching rate.

This is not yet a common full-energy Bastin integral or a Středa surface/sea representation. No
zero-temperature distributional derivative, zero-broadening, DC, disorder, trace-per-volume, or
thermodynamic-limit statement is made here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open SecondQuantization.Fermionic.Lattice
open MeasureTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site ι E : Type*}
variable [Fintype Site]
variable [LinearOrder Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- The current matrix elements and retarded-resolvent factor of one finite directional Bastin
transition, with the occupation difference removed. -/
noncomputable def finiteKuboBastinDirectionalTransitionFactor
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) : ℂ :=
  inner ℂ (data.basis mn.1)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K (data.basis mn.2)) *
    inner ℂ (data.basis mn.2)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K (data.basis mn.1)) *
    inner ℂ (data.basis mn.2)
      (QuantumTheory.Transport.retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis mn.2))

omit [Fintype ι] in
theorem finiteKuboBastinDirectionalTransitionFactor_eq_vertex
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    finiteKuboBastinDirectionalTransitionFactor
        system data geometry direction K q omega eta mn =
      purePointKuboBastinVertexTransitionFactor system data
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        omega eta mn := by
  rfl

noncomputable def finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) : ℂ :=
  -(∫ energy in data.energy mn.2..data.energy mn.1,
      interpolation.occupationDerivative energy) *
    finiteKuboBastinDirectionalTransitionFactor
      system data geometry direction K q omega eta mn

omit [Fintype ι] in
theorem finiteKuboBastinOccupationResolvedDirectionalCurrentTerm_eq_vertex
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
        system data interpolation geometry direction K q omega eta mn =
      purePointKuboBastinOccupationResolvedVertexTerm system data interpolation
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        omega eta mn := by
  rfl

omit [Fintype ι] in
theorem finiteKuboBastinSpectralDirectionalCurrentTerm_eq_occupationResolved
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    finiteKuboBastinSpectralDirectionalCurrentTerm
        system data geometry direction K q omega eta mn =
      finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
        system data interpolation geometry direction K q omega eta mn := by
  unfold finiteKuboBastinSpectralDirectionalCurrentTerm
    finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
    finiteKuboBastinDirectionalTransitionFactor
  rw [interpolation.probabilityDifference_eq_integral system mn.1 mn.2]
  ring

noncomputable def finiteKuboBastinOccupationResolvedDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℂ :=
  ((∑ mn : ι × ι,
      finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
        system data interpolation geometry direction K q omega eta mn) +
      purePointNormalizedExpectation system data
        (boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization convention omega eta

theorem finiteKuboBastinSpectralDirectionalConductivity_eq_occupationResolved
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention =
      finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta := by
  unfold finiteKuboBastinSpectralDirectionalConductivity
    finiteKuboBastinOccupationResolvedDirectionalConductivity
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteKuboBastinSpectralDirectionalCurrentTerm_eq_occupationResolved
    system data interpolation geometry direction K q omega eta mn

/-- The occupation-resolved response remains connected directly to the upstream causal Kubo and
spectral Kubo–Bastin derivation at fixed positive switching rate. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_eq_occupationResolved
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (heta : 0 < eta) :
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta := by
  calc
    _ = finiteKuboGreenwoodDirectionalConductivity
        convention system data geometry direction K q omega eta :=
      infiniteTimeAdiabaticDirectionalConductivity_eq_finiteKuboGreenwood
        convention system data geometry direction K q omega eta heta
    _ = finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention :=
      finiteKuboGreenwoodDirectionalConductivity_eq_bastinSpectral
        system data geometry direction K q omega eta convention heta
    _ = finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteKuboBastinSpectralDirectionalConductivity_eq_occupationResolved
        convention system data interpolation geometry direction K q omega eta

end
end Transport
end Fermionic
end SecondQuantization

import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral
import LeanCondensedMatter.Transport.KuboBastin.Occupation

set_option linter.style.header false

/-!
# Fermionic directional occupation-resolved Kubo–Bastin response

This module specializes the generic occupation interpolation and measured/source Kubo–Bastin response
to finite-lattice directional charge currents, including the Peierls contact term and finite-volume
normalization.

For each directional transition, the discrete probability difference is replaced by the oriented
energy integral of the supplied occupation derivative. The resulting response remains connected to
the causal Kubo and spectral Kubo–Bastin representations at fixed positive switching rate.

No common full-energy Bastin integral, Středa surface/sea decomposition, zero-temperature
distributional derivative, zero-broadening limit, DC limit, disorder average, trace per unit volume,
or thermodynamic limit is asserted here.
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

/-- One finite directional Kubo–Bastin transition with its discrete occupation difference replaced
by an oriented energy integral of the occupation derivative. -/
noncomputable def finiteKuboBastinOccupationResolvedDirectionalCurrentTerm
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) : ℂ :=
  purePointKuboBastinOccupationResolvedVertexTerm system data interpolation
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    omega eta mn

/-- The complete finite directional conductivity after replacing every discrete probability
difference by its oriented occupation-derivative integral. The contact term and finite-volume
normalization remain unchanged. -/
noncomputable def finiteKuboBastinOccupationResolvedDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℂ :=
  finiteKuboBastinOccupationResolvedVertexResponse system data interpolation
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta *
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
  exact congrArg
    (fun response : ℂ =>
      response * finiteVolumeConductivityNormalization convention omega eta)
    (finiteKuboBastinSpectralVertexResponse_eq_occupationResolved
      system data interpolation
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      omega eta)

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

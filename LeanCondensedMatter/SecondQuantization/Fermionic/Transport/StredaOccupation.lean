import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinTrace
import LeanCondensedMatter.Transport.OccupationInterpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Occupation interpolation boundary for the regularized Středa program

The finite Kubo–Bastin response inherited from the causal Kubo chain is expressed using discrete
pure-point probabilities `pₘ`. A physical Středa energy integral instead requires a differentiable
occupation function `f(E)`. These are not interchangeable by definition: the bridge must state that
`f(Eₘ) = pₘ` on the supplied energy spectrum and must provide the integrability needed by the
fundamental theorem of calculus.

This module records that missing boundary. For every transition it proves

```text
pₘ - pₙ = ∫_[Eₙ,Eₘ] f'(E) dE
```

and rewrites the complete finite Kubo–Bastin conductivity using these oriented occupation-derivative
integrals. The result remains exactly equal to the response derived from time-dependent
perturbation theory at fixed positive switching rate.

This is not yet a common full-energy Bastin integral and therefore is not yet the concrete
surface/sea representation required to close issue #368. The next layer must combine the finite
transition intervals into a common energy kernel and use the resolvent energy-derivative identities.
No zero-temperature distributional derivative, zero-broadening, DC, disorder, trace-per-volume, or
thermodynamic-limit claim is made here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open SecondQuantization.Fermionic.Lattice

open MeasureTheory QuantumTheory.LinearResponse QuantumTheory.Transport
open SecondQuantization.Fermionic.Field

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- The current matrix elements and retarded resolvent factor of one finite Bastin transition,
with the occupation difference removed. -/
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

/-- One finite Kubo–Bastin transition with its discrete occupation difference replaced by an
oriented energy integral of the occupation derivative. -/
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

/-- The occupation-resolved transition is exactly the existing finite retarded-resolvent
transition. -/
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

variable [Fintype ι]

/-- The complete finite conductivity after replacing every discrete probability difference by its
oriented occupation-derivative integral. The contact term and finite-volume normalization remain
unchanged. -/
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

/-- The finite spectral Bastin conductivity equals its occupation-resolved transition-integral
form. -/
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

/-- The named ordinary-trace finite Kubo–Bastin response equals the occupation-resolved finite
transition-integral form. -/
theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_occupationResolved
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta := by
  calc
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention :=
      finiteDimensionalKuboBastinDirectionalConductivity_eq_spectral
        convention system data geometry direction K q omega eta
    _ = finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteKuboBastinSpectralDirectionalConductivity_eq_occupationResolved
        convention system data interpolation geometry direction K q omega eta

/-- The occupation-resolved response remains connected to the upstream causal Kubo derivation at
fixed positive switching rate. -/
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
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta :=
      infiniteTimeAdiabaticDirectionalConductivity_eq_finiteDimensionalKuboBastin
        convention system data geometry direction K q omega eta heta
    _ = finiteKuboBastinOccupationResolvedDirectionalConductivity
        convention system data interpolation geometry direction K q omega eta :=
      finiteDimensionalKuboBastinDirectionalConductivity_eq_occupationResolved
        convention system data interpolation geometry direction K q omega eta

end
end Transport
end Fermionic
end SecondQuantization

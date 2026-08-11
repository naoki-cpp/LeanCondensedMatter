import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaIntegration
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
namespace Field

open MeasureTheory QuantumTheory.LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
variable (system : BoundedFreeSystem H)

/-- A differentiable complex occupation function reproducing the discrete pure-point
probabilities on every supplied energy eigenvalue. -/
structure PurePointOccupationInterpolation
    (data : PurePointLehmannData system ι) where
  /-- Continuous-energy occupation used by the later Bastin integral. -/
  occupation : ℝ → ℂ
  /-- Energy derivative of the occupation. -/
  occupationDerivative : ℝ → ℂ
  /-- The continuous occupation reproduces every discrete spectral probability. -/
  occupation_matches_probability :
    ∀ i, occupation (data.energy i) = (data.probability i : ℂ)
  /-- Pointwise differentiability, kept stronger than necessary for the first finite bridge. -/
  occupation_hasDerivAt :
    ∀ energy, HasDerivAt occupation (occupationDerivative energy) energy
  /-- The derivative is integrable on every oriented transition-energy interval. -/
  occupationDerivative_intervalIntegrable :
    ∀ m n, IntervalIntegrable occupationDerivative volume
      (data.energy n) (data.energy m)

/-- The occupation difference of two energy eigenstates is the oriented integral of the
occupation derivative between their energies. -/
theorem PurePointOccupationInterpolation.probability_sub_eq_integral
    {data : PurePointLehmannData system ι}
    (interpolation : PurePointOccupationInterpolation system data)
    (m n : ι) :
    (data.probability m : ℂ) - (data.probability n : ℂ) =
      ∫ energy in data.energy n..data.energy m,
        interpolation.occupationDerivative energy := by
  rw [← interpolation.occupation_matches_probability m,
    ← interpolation.occupation_matches_probability n]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun energy _ => interpolation.occupation_hasDerivAt energy)
    (interpolation.occupationDerivative_intervalIntegrable m n)

/-- The same transition identity in the casted real-difference form used by the Lehmann weight. -/
theorem PurePointOccupationInterpolation.probabilityDifference_eq_integral
    {data : PurePointLehmannData system ι}
    (interpolation : PurePointOccupationInterpolation system data)
    (m n : ι) :
    (((data.probability m - data.probability n : ℝ) : ℂ)) =
      ∫ energy in data.energy n..data.energy m,
        interpolation.occupationDerivative energy := by
  simpa using interpolation.probability_sub_eq_integral system m n

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
end Field
end Fermionic
end SecondQuantization

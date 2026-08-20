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

This module records that boundary first for arbitrary measured/source response vertices and an
explicit observable-variation/contact term. For every transition it proves

```text
pₘ - pₙ = ∫_[Eₙ,Eₘ] f'(E) dE
```

and rewrites the complete finite generalized Kubo–Bastin response using these oriented
occupation-derivative integrals. The existing directional charge-current conductivity path is then
retained as a downstream specialization with its Peierls contact and finite-volume normalization.

This is not yet a common full-energy Bastin integral and therefore is not yet the concrete
surface/sea representation required by `RegularizedStredaRepresentation`. The next layer combines
the finite transition intervals into a common energy kernel. Identifying that kernel or the static
response with the canonical traced Středa/Bastin integral remains a separate Ward/energy-
representation problem.

No zero-temperature distributional derivative, zero-broadening, DC, disorder, trace-per-volume, or
thermodynamic-limit claim is made here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open SecondQuantization.Fermionic.Lattice

open MeasureTheory QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site : Type*}
variable [Fintype Site]

/-- Matrix elements and retarded-resolvent factor of one finite generalized Bastin transition,
with the occupation difference removed. -/
noncomputable def finiteKuboBastinVertexTransitionFactor
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  inner ℂ (data.basis mn.1) (measured (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (source (data.basis mn.1)) *
    inner ℂ (data.basis mn.2)
      (QuantumTheory.Transport.retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis mn.2))

/-- One generalized Kubo–Bastin transition with its discrete occupation difference replaced by an
oriented energy integral of the occupation derivative. -/
noncomputable def finiteKuboBastinOccupationResolvedVertexTerm
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  -(∫ energy in data.energy mn.2..data.energy mn.1,
      interpolation.occupationDerivative energy) *
    finiteKuboBastinVertexTransitionFactor
      system data measured source omega eta mn

/-- The generalized spectral Bastin transition is exactly its occupation-resolved form. -/
theorem finiteKuboBastinSpectralVertexTerm_eq_occupationResolved
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) :
    finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn =
      finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  unfold finiteKuboBastinSpectralVertexTerm
    finiteKuboBastinOccupationResolvedVertexTerm
    finiteKuboBastinVertexTransitionFactor
  rw [interpolation.probabilityDifference_eq_integral system mn.1 mn.2]
  ring

variable [Fintype ι]

/-- Complete generalized response after replacing every discrete probability difference by its
oriented occupation-derivative integral. The explicit observable-variation/contact expectation is
kept unchanged. -/
noncomputable def finiteKuboBastinOccupationResolvedVertexResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) : ℂ :=
  (∑ mn : ι × ι,
      finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn) +
    purePointNormalizedExpectation system data observableVariation

/-- The generalized finite spectral Bastin response equals its occupation-resolved form. -/
theorem finiteKuboBastinSpectralVertexResponse_eq_occupationResolved
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta =
      finiteKuboBastinOccupationResolvedVertexResponse
        system data interpolation measured source observableVariation omega eta := by
  unfold finiteKuboBastinSpectralVertexResponse
    finiteKuboBastinOccupationResolvedVertexResponse
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteKuboBastinSpectralVertexTerm_eq_occupationResolved
    system data interpolation measured source omega eta mn

/-- Occupation-resolved generalized response attached directly to a neutral response channel. -/
noncomputable def finiteKuboBastinOccupationResolvedChannelResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinOccupationResolvedVertexResponse system data interpolation
    channel.measured channel.source channel.observableVariation omega eta

/-- The neutral finite spectral channel response equals its occupation-resolved form. -/
theorem finiteKuboBastinSpectralChannelResponse_eq_occupationResolved
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) :
    finiteKuboBastinSpectralChannelResponse system data channel omega eta =
      finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta := by
  simpa [finiteKuboBastinSpectralChannelResponse,
    finiteKuboBastinOccupationResolvedChannelResponse] using
    finiteKuboBastinSpectralVertexResponse_eq_occupationResolved
      system data interpolation channel.measured channel.source
        channel.observableVariation omega eta

variable {E : Type*}
variable [LinearOrder Site]
variable [AddCommGroup E] [Module ℝ E]

/-- The current matrix elements and retarded resolvent factor of one finite directional Bastin
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

/-- The directional transition factor is the generalized measured/source factor specialized to the
same directional charge current at both vertices. -/
omit [Fintype ι] in
theorem finiteKuboBastinDirectionalTransitionFactor_eq_vertex
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ)
    (mn : ι × ι) :
    finiteKuboBastinDirectionalTransitionFactor
        system data geometry direction K q omega eta mn =
      finiteKuboBastinVertexTransitionFactor system data
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        omega eta mn := by
  rfl

/-- One finite directional Kubo–Bastin transition with its discrete occupation difference replaced
by an oriented energy integral of the occupation derivative. -/
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

/-- The directional occupation-resolved term is the generalized vertex term specialized to the
same directional charge current at both vertices. -/
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
      finiteKuboBastinOccupationResolvedVertexTerm system data interpolation
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        omega eta mn := by
  rfl

/-- The occupation-resolved directional transition is exactly the existing finite
retarded-resolvent transition. -/
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

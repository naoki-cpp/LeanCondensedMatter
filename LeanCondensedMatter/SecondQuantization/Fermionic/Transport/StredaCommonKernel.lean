import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StredaOccupation

set_option linter.style.header false

/-!
# Common energy kernel for finite Kubo–Bastin response

Finite transition intervals are localized on the full energy axis and summed into one integrable
piecewise kernel.  The construction is first stated for arbitrary measured/source vertices and an
explicit observable-variation/contact term carried by the generalized response channel.  The
existing directional charge-current conductivity remains a downstream specialization with its
Peierls contact and finite-volume normalization.

The common kernel is generally discontinuous at spectral energies.  It is therefore not itself the
smooth Středa primitive required by `RegularizedStredaRepresentation`, and equality with the
canonical traced Bastin energy integral is not asserted here.  That identification remains a
separate Ward/energy-representation theorem.
-/

namespace SecondQuantization.Fermionic.Transport

open SecondQuantization.Fermionic.Lattice
open MeasureTheory QuantumTheory.LinearResponse QuantumTheory.Transport Set

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

variable {Site ι : Type*}
variable [Fintype Site]

/-- Full-line localized integrand associated with one generalized Bastin transition. -/
noncomputable def finiteKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) (energy : ℝ) : ℂ :=
  orientedIntervalIntegrand
    ((-finiteKuboBastinVertexTransitionFactor
      system data measured source omega eta mn) •
      interpolation.occupationDerivative)
    (data.energy mn.2) (data.energy mn.1) energy

theorem integrable_finiteKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) :
    Integrable (finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn) := by
  apply integrable_orientedIntervalIntegrand
  exact (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul
    (-finiteKuboBastinVertexTransitionFactor
      system data measured source omega eta mn)

theorem integral_finiteKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (mn : ι × ι) :
    (∫ energy : ℝ, finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn energy) =
      finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  let factor := finiteKuboBastinVertexTransitionFactor
    system data measured source omega eta mn
  have hint : IntervalIntegrable ((-factor) • interpolation.occupationDerivative)
      volume (data.energy mn.2) (data.energy mn.1) :=
    (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul (-factor)
  rw [show finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn =
      orientedIntervalIntegrand ((-factor) • interpolation.occupationDerivative)
        (data.energy mn.2) (data.energy mn.1) by rfl]
  rw [integral_orientedIntervalIntegrand _ _ _ hint]
  change (∫ energy in data.energy mn.2..data.energy mn.1,
      (-factor) • interpolation.occupationDerivative energy) = _
  rw [intervalIntegral.integral_smul]
  unfold finiteKuboBastinOccupationResolvedVertexTerm
  simp only [smul_eq_mul]
  ring

variable [Fintype ι]

/-- Finite sum of all generalized localized transition integrands on the full energy axis. -/
noncomputable def finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι, finiteKuboBastinCommonVertexTransitionIntegrand
    system data interpolation measured source omega eta mn energy

theorem integrable_finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    Integrable (finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta) := by
  unfold finiteKuboBastinCommonVertexEnergyKernel
  apply integrable_finsetSum
  intro mn _
  exact integrable_finiteKuboBastinCommonVertexTransitionIntegrand
    system data interpolation measured source omega eta mn

theorem integral_finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    (∫ energy : ℝ, finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta energy) =
      ∑ mn : ι × ι, finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  unfold finiteKuboBastinCommonVertexEnergyKernel
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro mn _
    exact integral_finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn
  · intro mn _
    exact integrable_finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn

/-- Generalized common-energy response, with the explicit observable-variation/contact expectation
kept outside the energy kernel. -/
noncomputable def finiteKuboBastinCommonEnergyVertexResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) : ℂ :=
  (∫ energy : ℝ, finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta energy) +
    purePointNormalizedExpectation system data observableVariation

/-- The generalized occupation-resolved response equals its common-energy-kernel form. -/
theorem finiteKuboBastinOccupationResolvedVertexResponse_eq_commonEnergy
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (omega eta : ℝ) :
    finiteKuboBastinOccupationResolvedVertexResponse system data interpolation
        measured source observableVariation omega eta =
      finiteKuboBastinCommonEnergyVertexResponse system data interpolation
        measured source observableVariation omega eta := by
  unfold finiteKuboBastinOccupationResolvedVertexResponse
    finiteKuboBastinCommonEnergyVertexResponse
  rw [integral_finiteKuboBastinCommonVertexEnergyKernel]

/-- Generalized common-energy response attached directly to a neutral response channel. -/
noncomputable def finiteKuboBastinCommonEnergyChannelResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinCommonEnergyVertexResponse system data interpolation
    channel.measured channel.source channel.observableVariation omega eta

/-- The generalized spectral channel response equals its common-energy-kernel representation. -/
theorem finiteKuboBastinSpectralChannelResponse_eq_commonEnergy
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
    (omega eta : ℝ) :
    finiteKuboBastinSpectralChannelResponse system data channel omega eta =
      finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta := by
  calc
    _ = finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta :=
      finiteKuboBastinSpectralChannelResponse_eq_occupationResolved
        system data interpolation channel omega eta
    _ = finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta := by
      simpa [finiteKuboBastinOccupationResolvedChannelResponse,
        finiteKuboBastinCommonEnergyChannelResponse] using
        finiteKuboBastinOccupationResolvedVertexResponse_eq_commonEnergy
          system data interpolation channel.measured channel.source
            channel.observableVariation omega eta

variable {E : Type*}
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

/-- The directional localized transition integrand is the generalized common-energy integrand
specialized to the same directional current at both vertices. -/
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
      finiteKuboBastinCommonVertexTransitionIntegrand system data interpolation
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

/-- The finite sum of all localized directional transition integrands on the full energy axis. -/
noncomputable def finiteKuboBastinCommonEnergyKernel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι, finiteKuboBastinCommonTransitionIntegrand
    system data interpolation geometry direction K q omega eta mn energy

/-- The directional common-energy kernel is the generalized vertex kernel specialized to the same
directional current at both vertices. -/
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

end SecondQuantization.Fermionic.Transport

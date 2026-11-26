import LeanCondensedMatter.Models.RashbaExchange.FiniteMomentumSpinResponse
import LeanCondensedMatter.Models.RashbaExchange.RealSpaceHopping
import LeanCondensedMatter.QuantumTheory.ConservationLaw
import LeanCondensedMatter.QuantumTheory.LinearResponse.Frequency.InfiniteTime
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.FrequencyDomain
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Table

set_option linter.style.header false

/-!
# Rashba spin displacement: conditional proper-current bridge (R4)

The generic symmetric-localization identity already gives, for any one-body
position-like observable `X` and spin observable `S(n)`,

```text
δ_H({X,S(n)}/2) = {δ_H(X),S(n)}/2 + {X,δ_H(S(n))}/2.
```

We specialize that existing theorem to the *actual* finite Rashba momentum-grid
Hamiltonian and spin operator and transport it to the full finite Fock space.
The second contribution is the torque-dipole operator.

A finite sample of momentum points does **not** itself provide a physical position
operator. Identifying `δ_H(X)` with the momentum-derivative velocity is therefore
an explicit hypothesis, never silently inferred from a grid coordinate.
In particular, none of these identities proves the local torque-divergence or
boundary conditions needed to interpret the result as a locally conserved
Shi--Zhang--Xiao--Niu proper spin current. The distinct localization correction
`ConservationLaw.localizationCorrectionCurrentFlux` is not equated to a torque dipole.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.SpinfulLattice
open QuantumTheory.ConservationLaw
open SecondQuantization.Fermionic.Lattice

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Grid : Type*} [Fintype Grid]

/-- Symmetric spin displacement for a supplied position-like one-body observable.
The localization operation is owned by the existing general conservation-law layer. -/
noncomputable def finiteRashbaMomentumSpinDisplacement
    (spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ)) :
    (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ) :=
  _root_.ConservationLaw.localizedQuantityFunctional
    (LinearMap.id :
      ((SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ)) →ₗ[ℂ]
        ((SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ)))
    (spinOneBodyLinear spinScale component) position

/-- The existing general local-quantity identity, specialized to the finite Rashba
Hamiltonian and physical spin operator, gives transport plus spin torque. -/
theorem finiteRashbaMomentumSpinDisplacement_balance
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ)) :
    heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (finiteRashbaMomentumSpinDisplacement spinScale component position) =
      QuantumTheory.ConservationLaw.heisenbergTransportFunctional hbar (finiteRashbaMomentumHamiltonian params momentum)
          LinearMap.id (spinOneBodyLinear spinScale component) position +
      QuantumTheory.ConservationLaw.heisenbergSourceFunctional hbar (finiteRashbaMomentumHamiltonian params momentum)
          LinearMap.id (spinOneBodyLinear spinScale component) position := by
  exact heisenbergEvolution_symmetrizedProduct
    hbar (finiteRashbaMomentumHamiltonian params momentum)
    position (spinOneBodyLinear spinScale component)

/-- Heisenberg evolution of a spin displacement separates velocity-generated
spin transport from the explicitly nonconserved spin-torque contribution.
No position/velocity identification is assumed here. -/
theorem finiteRashbaMomentumSpinDisplacement_heisenberg_decomposition
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ)) :
    heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (finiteRashbaMomentumSpinDisplacement spinScale component position) =
      LinearMap.symmetrizedProduct (K := ℂ)
        (heisenbergEvolution hbar
          (finiteRashbaMomentumHamiltonian params momentum) position)
        (spinOneBodyLinear spinScale component) +
      LinearMap.symmetrizedProduct (K := ℂ) position
        (heisenbergEvolution hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (spinOneBodyLinear spinScale component)) := by
  exact heisenbergEvolution_symmetrizedProduct
    hbar (finiteRashbaMomentumHamiltonian params momentum)
    position (spinOneBodyLinear spinScale component)

/-- If an independently justified position representation has the *same*
Heisenberg velocity as the Rashba momentum derivative, the spin-displacement
derivative is conventional spin current plus the torque dipole. -/
theorem finiteRashbaMomentumSpinDisplacement_eq_spinCurrent_add_torque
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (direction : Fin 2)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ))
    (hvelocity :
      heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum) position =
      finiteRashbaMomentumVelocity params momentum direction) :
    heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (finiteRashbaMomentumSpinDisplacement spinScale component position) =
      LinearMap.symmetrizedProduct (K := ℂ)
        (finiteRashbaMomentumVelocity params momentum direction)
        (spinOneBodyLinear spinScale component) +
      LinearMap.symmetrizedProduct (K := ℂ) position
        (heisenbergEvolution hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (spinOneBodyLinear spinScale component)) := by
  rw [finiteRashbaMomentumSpinDisplacement_heisenberg_decomposition, hvelocity]

/-- The conditional proper-current decomposition survives the canonical finite
Fock lift. The conventional contribution is the *existing* boundedSpinCurrentLinear,
and the remaining observable is a bounded torque dipole. -/
theorem finiteRashbaMomentumSpinDisplacement_fock_decomposition
    [LinearOrder Grid]
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (direction : Fin 2)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ))
    (hvelocity :
      heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum) position =
      finiteRashbaMomentumVelocity params momentum direction) :
    boundedOneBodyOperator
        (heisenbergEvolution hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (finiteRashbaMomentumSpinDisplacement spinScale component position)) =
      SecondQuantization.Fermionic.Transport.boundedSpinCurrentLinear
          (finiteRashbaMomentumVelocity params momentum direction)
          spinScale component +
        boundedOneBodyOperator
          (LinearMap.symmetrizedProduct (K := ℂ) position
            (heisenbergEvolution hbar
              (finiteRashbaMomentumHamiltonian params momentum)
              (spinOneBodyLinear spinScale component))) := by
  rw [← hvelocity]
  exact map_heisenbergEvolution_symmetrizedProduct
    (boundedOneBodyOperator (Site := SpinfulSite Grid)).toLinearMap hbar (finiteRashbaMomentumHamiltonian params momentum) position
    (spinOneBodyLinear spinScale component)

/-- The physical spin-displacement derivative, supplied at the same momentum
grid as the conventional Rashba spin/charge channel, is a candidate measured
proper current. Its source and contact observable are inherited unchanged from
the existing channel; no separate Kubo infrastructure is introduced.

The supplied `position` is not derived from the finite momentum labels. -/
noncomputable def finiteRashbaMomentumSpinDisplacementResponseChannel
    [LinearOrder Grid]
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (charge : ℂ)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ))
    (contact :
      FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Grid)) :
    QuantumTheory.LinearResponse.ResponseChannel
      (FiniteLatticeHilbertFock (SpinfulSite Grid)) :=
  { finiteRashbaMomentumSpinChargeChannel params momentum spinScale component
        measured source charge contact with
    measured :=
      boundedOneBodyOperator
        (heisenbergEvolution hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (finiteRashbaMomentumSpinDisplacement spinScale component position)) }

/-- At finite momentum-grid/Fock cutoff, under the explicitly assumed
`δ_H X_i = v_i` identity, the *retarded* spin-displacement/charge kernel
is the conventional spin/charge kernel plus the torque-dipole/charge kernel.
This is a model-level consequence of the already-proved Fock observable
decomposition and the existing measured-observable linearity of Kubo response.

Contact terms are separate: this identity concerns the retarded kernel, not
a full electric-field conductivity or the source-dependent observable variation.
No finite-grid position operator or local torque-divergence law is asserted. -/
theorem finiteRashbaMomentumSpinDisplacement_retardedKernel_eq_conventional_add_torque
    [LinearOrder Grid]
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar)
    (spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (charge : ℂ)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ))
    (hvelocity :
      heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum) position =
      finiteRashbaMomentumVelocity params momentum measured)
    (contact :
      FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Grid))
    (expectation :
      QuantumTheory.LinearResponse.NormalizedExpectation
        (FiniteLatticeHilbertFock (SpinfulSite Grid)))
    (t s : ℝ) :
    (finiteRashbaMomentumSpinDisplacementResponseChannel
        params momentum hbar spinScale component measured source charge position contact).retardedKernel
        (QuantumTheory.LinearResponse.freePropagatorGroup
          (finiteRashbaMomentumFreeSystem params momentum hbar hhbar))
        hbar expectation t s =
      (finiteRashbaMomentumSpinChargeChannel
          params momentum spinScale component measured source charge contact).retardedKernel
          (QuantumTheory.LinearResponse.freePropagatorGroup
            (finiteRashbaMomentumFreeSystem params momentum hbar hhbar))
          hbar expectation t s +
      QuantumTheory.LinearResponse.retardedSusceptibility
        (QuantumTheory.LinearResponse.freePropagatorGroup
          (finiteRashbaMomentumFreeSystem params momentum hbar hhbar))
        hbar expectation
        (boundedOneBodyOperator
          (LinearMap.symmetrizedProduct (K := ℂ) position
            (heisenbergEvolution hbar
              (finiteRashbaMomentumHamiltonian params momentum)
              (spinOneBodyLinear spinScale component))))
        (boundedOneBodyOperator
          (charge • finiteRashbaMomentumVelocity params momentum source))
        t s := by
  let U := QuantumTheory.LinearResponse.freePropagatorGroup
    (finiteRashbaMomentumFreeSystem params momentum hbar hhbar)
  let B := boundedOneBodyOperator
    (charge • finiteRashbaMomentumVelocity params momentum source)
  let J := SecondQuantization.Fermionic.Transport.boundedSpinCurrentLinear
    (finiteRashbaMomentumVelocity params momentum measured) spinScale component
  let T := boundedOneBodyOperator
    (LinearMap.symmetrizedProduct (K := ℂ) position
      (heisenbergEvolution hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (spinOneBodyLinear spinScale component)))
  change QuantumTheory.LinearResponse.retardedSusceptibility U hbar expectation
      (boundedOneBodyOperator
        (heisenbergEvolution hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (finiteRashbaMomentumSpinDisplacement spinScale component position)))
      B t s =
    QuantumTheory.LinearResponse.retardedSusceptibility U hbar expectation J B t s +
      QuantumTheory.LinearResponse.retardedSusceptibility U hbar expectation T B t s
  rw [finiteRashbaMomentumSpinDisplacement_fock_decomposition
    params momentum hbar spinScale component measured position hvelocity]
  exact (QuantumTheory.LinearResponse.retardedSusceptibilityMeasuredLinearMap
    U hbar expectation B t s).map_add J T

/-! ## Real-space proper-current bridge -/

/-- On an arbitrary finite planar Rashba lattice, the spin-displacement
derivative is the conventional spin current plus torque dipole, with position
and velocity supplied by the same physical geometry and hopping Hamiltonian.
No momentum-derivative/position compatibility hypothesis is required.
This is a global operator identity, not a local source-free continuity law. -/
theorem realSpaceRashbaSpinDisplacement_fock_decomposition
    {Site : Type*} [LinearOrder Site] [Fintype Site]
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (direction : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace) :
    let H := (realSpaceRashbaHopping geometry bond onsite exchange).operator
    let X := (spinfulGeometry geometry).directionalPosition direction
    let S := spinOneBodyLinear (Site := Site) spinScale component
    boundedOneBodyOperator
        (heisenbergEvolution hbar H
          (LinearMap.symmetrizedProduct (K := ℂ) X S)) =
      SecondQuantization.Fermionic.Transport.boundedSpinCurrentLinear
          (heisenbergEvolution hbar H X) spinScale component +
        boundedOneBodyOperator
          (LinearMap.symmetrizedProduct (K := ℂ) X
            (heisenbergEvolution hbar H S)) := by
  exact map_heisenbergEvolution_symmetrizedProduct
    (boundedOneBodyOperator (Site := SpinfulSite Site)).toLinearMap hbar (realSpaceRashbaHopping geometry bond onsite exchange).operator
    ((spinfulGeometry geometry).directionalPosition direction)
    (spinOneBodyLinear spinScale component)

/-- Free dynamics for the same finite real-space Rashba Hamiltonian used in
the displacement and Peierls source. Hermiticity is proved by the hopping
construction, not assumed independently. -/
noncomputable def realSpaceRashbaFreeSystem
    {Site : Type*} [LinearOrder Site] [Fintype Site]
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar) :
    QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock (SpinfulSite Site)) where
  hamiltonian := ⟨boundedHoppingHamiltonian (realSpaceRashbaHopping geometry bond onsite exchange),
    realSpaceRashbaHamiltonian_isSelfAdjoint geometry bond onsite exchange⟩
  hbar := hbar
  hbar_pos := hhbar

/-- The real-space Rashba proper-current/charge channel uses the generic
finite-lattice spin-displacement response with the actual Rashba hopping.
Set `sourceValue = f t` for a causal response to profile `f` at time `t`,
or `sourceValue = 1` for source-normalized frequency/Lehmann response.
Use `realSpaceRashbaFreeSystem` with the same hopping inputs and hbar. -/
noncomputable def realSpaceRashbaSpinDisplacementResponseChannel
    {Site : Type*} [LinearOrder Site] [Fintype Site]
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (measured source : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hbar q spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (sourceValue : ℝ) :
    QuantumTheory.LinearResponse.ResponseChannel
      (FiniteLatticeHilbertFock (SpinfulSite Site)) :=
  SecondQuantization.Fermionic.Transport.boundedSpinDisplacementDirectionalResponseChannel
    geometry measured source (realSpaceRashbaHopping geometry bond onsite exchange)
    hbar q spinScale component sourceValue

/-- The stationary, source-normalized finite-time Rashba proper-current
response is the displacement susceptibility's upper boundary minus its
phase-weighted transform multiplied by the adiabatic exponent.
The physical contact cancels the equal-time lower boundary. -/
theorem realSpaceRashbaSpinDisplacement_finiteTimeAdiabaticResponse
    {Site : Type*} [LinearOrder Site] [Fintype Site]
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (measured source : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hbar q spinScale : ℝ) (hhbar : 0 < hbar)
    (component : QuantumTheory.SpinHalf.SpinSpace)
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (hstationary : QuantumTheory.LinearResponse.IsStationary
      (QuantumTheory.LinearResponse.freePropagatorGroup
        (realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar)) expectation)
    (ω η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
    let channel := realSpaceRashbaSpinDisplacementResponseChannel
      geometry bond onsite exchange measured source hbar q spinScale component 1
    let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
      ((spinfulGeometry geometry).directionalPosition measured)
      (spinOneBodyLinear (Site := Site) spinScale component))
    let K := fun τ => QuantumTheory.LinearResponse.commutatorSusceptibility
      (QuantumTheory.LinearResponse.freePropagatorGroup system) hbar
      expectation D channel.source τ 0
    channel.finiteTimeAdiabaticResponse (QuantumTheory.LinearResponse.freePropagatorGroup system)
      hbar expectation ω η T =
      QuantumTheory.LinearResponse.adiabaticFrequencyPhase ω η T * K T -
        (Complex.I * (ω : ℂ) - (η : ℂ)) *
          QuantumTheory.LinearResponse.finiteTimeAdiabaticTransform K ω η T := by
  let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
  let channel := realSpaceRashbaSpinDisplacementResponseChannel
    geometry bond onsite exchange measured source hbar q spinScale component 1
  let D := LinearMap.symmetrizedProduct (K := ℂ)
    ((spinfulGeometry geometry).directionalPosition measured)
    (spinOneBodyLinear (Site := Site) spinScale component)
  have hJ : channel.measured =
      (Complex.I / (system.hbar : ℂ)) •
        ⁅system.hamiltonian.1, boundedOneBodyOperator D⁆ := by
    let H := (realSpaceRashbaHopping geometry bond onsite exchange).operator
    change boundedOneBodyOperator
        (QuantumTheory.ConservationLaw.heisenbergEvolution hbar H D) =
      (Complex.I / (hbar : ℂ)) • ⁅boundedOneBodyOperator H, boundedOneBodyOperator D⁆
    exact map_heisenbergEvolution (boundedOneBodyOperator (Site := SpinfulSite Site)) hbar H D
  have hC : channel.observableVariation =
      (Complex.I / (system.hbar : ℂ)) • ⁅-channel.source, boundedOneBodyOperator D⁆ := by
    change (((1 : ℝ) : ℂ) • ((Complex.I / (hbar : ℂ)) •
      ⁅-channel.source, boundedOneBodyOperator D⁆)) =
        (Complex.I / (hbar : ℂ)) • ⁅-channel.source, boundedOneBodyOperator D⁆
    rw [Complex.ofReal_one, one_smul]
  exact channel.finiteTimeAdiabaticResponse_of_displacement system expectation
    hstationary (boundedOneBodyOperator D) hJ hC ω η hT

/-- At fixed positive switching rate the stationary proper-current/charge
response of the actual finite planar Rashba hopping is the displacement
susceptibility multiplied by minus the adiabatic exponent. This takes the
observation-time limit only, with no zero-rate or bulk/DC assertion. -/
theorem realSpaceRashbaSpinDisplacement_infiniteTimeAdiabaticResponse
    {Site : Type*} [LinearOrder Site] [Fintype Site]
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (measured source : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hbar q spinScale : ℝ) (hhbar : 0 < hbar)
    (component : QuantumTheory.SpinHalf.SpinSpace)
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (hstationary : QuantumTheory.LinearResponse.IsStationary
      (QuantumTheory.LinearResponse.freePropagatorGroup
        (realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar)) expectation)
    (ω η : ℝ) (hη : 0 < η) :
    let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
    let channel := realSpaceRashbaSpinDisplacementResponseChannel
      geometry bond onsite exchange measured source hbar q spinScale component 1
    let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
      ((spinfulGeometry geometry).directionalPosition measured)
      (spinOneBodyLinear (Site := Site) spinScale component))
    channel.infiniteTimeAdiabaticResponse (QuantumTheory.LinearResponse.freePropagatorGroup system)
      hbar expectation ω η =
      -(Complex.I * (ω : ℂ) - (η : ℂ)) *
        QuantumTheory.LinearResponse.adiabaticFrequencyDomainSusceptibility
          (QuantumTheory.LinearResponse.freePropagatorGroup system) hbar
          expectation D channel.source ω η := by
  let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
  let channel := realSpaceRashbaSpinDisplacementResponseChannel
    geometry bond onsite exchange measured source hbar q spinScale component 1
  let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
    ((spinfulGeometry geometry).directionalPosition measured)
    (spinOneBodyLinear (Site := Site) spinScale component))
  exact channel.infiniteTimeAdiabaticResponse_eq_of_displacement_boundary system expectation
    hstationary D ω η hη (fun T hT =>
      realSpaceRashbaSpinDisplacement_finiteTimeAdiabaticResponse
        geometry bond onsite exchange measured source hbar q spinScale hhbar
        component expectation hstationary ω η hT)

/-- The finite-volume electric-field response of the proper spin current.
The same vector-potential factor that occurs in the displacement-derivative
identity cancels the electric-field normalization, with the opposite sign.
The directions and spin component are arbitrary; transverse components
give the corresponding proper spin Hall conductivity. -/
theorem realSpaceRashbaSpinDisplacement_conductivity_eq
    {Site : Type*} [LinearOrder Site] [Fintype Site]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (measured source : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hbar q spinScale : ℝ) (hhbar : 0 < hbar)
    (component : QuantumTheory.SpinHalf.SpinSpace)
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (hstationary : QuantumTheory.LinearResponse.IsStationary
      (QuantumTheory.LinearResponse.freePropagatorGroup
        (realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar)) expectation)
    (ω η : ℝ) (hη : 0 < η) :
    let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
    let channel := realSpaceRashbaSpinDisplacementResponseChannel
      geometry bond onsite exchange measured source hbar q spinScale component 1
    let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
      ((spinfulGeometry geometry).directionalPosition measured)
      (spinOneBodyLinear (Site := Site) spinScale component))
    QuantumTheory.Transport.finiteVolumeConductivityFromVectorPotential volume ω η
      (channel.infiniteTimeAdiabaticResponse (QuantumTheory.LinearResponse.freePropagatorGroup system)
        hbar expectation ω η) =
      -QuantumTheory.LinearResponse.adiabaticFrequencyDomainSusceptibility
        (QuantumTheory.LinearResponse.freePropagatorGroup system) hbar
        expectation D channel.source ω η / (volume.volume : ℂ) := by
  dsimp only
  rw [realSpaceRashbaSpinDisplacement_infiniteTimeAdiabaticResponse
    geometry bond onsite exchange measured source hbar q spinScale hhbar
    component expectation hstationary ω η hη]
  have hz : Complex.I * (ω : ℂ) - (η : ℂ) =
      QuantumTheory.Transport.adiabaticElectricFieldFactor ω η := by
    rw [QuantumTheory.Transport.adiabaticElectricFieldFactor, sub_eq_add_neg, add_comm]
  rw [hz]
  exact QuantumTheory.Transport.finiteVolumeConductivityFromVectorPotential_neg_factor
    volume ω η (Or.inr (ne_of_gt hη)) _

/-- The finite-volume proper spin conductivity can be evaluated using the
existing scalar Lehmann table of the displacement and charge source. No
separate current/contact table is needed after the exact cancellation.
This theorem assumes supplied finite eigenbasis data; it is not a computed
nonzero benchmark or a zero-rate/thermodynamic limit. -/
theorem realSpaceRashbaSpinDisplacement_conductivity_eq_finiteLehmannTable
    {Site ι : Type*} [LinearOrder Site] [Fintype Site] [Fintype ι]
    (volume : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site (ℝ × ℝ))
    (bond : Site → Site → Option (ℝ × ℝ))
    (onsite exchange : Site → ℝ)
    (measured source : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (hbar q spinScale : ℝ) (hhbar : 0 < hbar)
    (component : QuantumTheory.SpinHalf.SpinSpace)
    (data : QuantumTheory.LinearResponse.EnergyEigenbasisLehmannData
      (realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar) ι)
    (ω η : ℝ) (hη : 0 < η) :
    let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
    let channel := realSpaceRashbaSpinDisplacementResponseChannel
      geometry bond onsite exchange measured source hbar q spinScale component 1
    let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
      ((spinfulGeometry geometry).directionalPosition measured)
      (spinOneBodyLinear (Site := Site) spinScale component))
    QuantumTheory.Transport.finiteVolumeConductivityFromVectorPotential volume ω η
      (channel.infiniteTimeAdiabaticResponse (QuantumTheory.LinearResponse.freePropagatorGroup system)
        hbar (QuantumTheory.LinearResponse.eigenbasisNormalizedExpectation system data) ω η) =
      -QuantumTheory.LinearResponse.finiteLehmannTableResponse hbar ω η
        (QuantumTheory.LinearResponse.finiteLehmannTableOfEigenbasis system data D channel.source) /
        (volume.volume : ℂ) := by
  let system := realSpaceRashbaFreeSystem geometry bond onsite exchange hbar hhbar
  let channel := realSpaceRashbaSpinDisplacementResponseChannel
    geometry bond onsite exchange measured source hbar q spinScale component 1
  let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
    ((spinfulGeometry geometry).directionalPosition measured)
    (spinOneBodyLinear (Site := Site) spinScale component))
  dsimp only
  rw [realSpaceRashbaSpinDisplacement_conductivity_eq volume
    geometry bond onsite exchange measured source hbar q spinScale hhbar
    component (QuantumTheory.LinearResponse.eigenbasisNormalizedExpectation system data)
    (QuantumTheory.LinearResponse.isStationary_eigenbasisNormalizedExpectation system data) ω η hη]
  change -QuantumTheory.LinearResponse.adiabaticFrequencyDomainSusceptibility
      (QuantumTheory.LinearResponse.freePropagatorGroup system) system.hbar
      (QuantumTheory.LinearResponse.eigenbasisNormalizedExpectation system data)
      D channel.source ω η / (volume.volume : ℂ) =
    -QuantumTheory.LinearResponse.finiteLehmannTableResponse system.hbar ω η
      (QuantumTheory.LinearResponse.finiteLehmannTableOfEigenbasis system data D channel.source) /
      (volume.volume : ℂ)
  rw [QuantumTheory.LinearResponse.finiteLehmannTableResponse_ofEigenbasis
      system data D channel.source ω η,
    QuantumTheory.LinearResponse.adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_lehmannSeries
      system data D channel.source ω η hη
      (QuantumTheory.LinearResponse.eigenbasisTimeDomainSummable_of_finite
        system data D channel.source)]

end
end QuantumTheory.Models.RashbaExchange

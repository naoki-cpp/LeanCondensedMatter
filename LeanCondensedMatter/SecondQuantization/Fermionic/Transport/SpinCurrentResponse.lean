import LeanCondensedMatter.QuantumTheory.SpinfulLattice
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricPeierls

set_option linter.style.header false

/-!
# Finite spin-current / electric-source cross response

This module gives a concrete generalized-current response on the finite spinful lattice
`Site × Fin 2`. A spin-space vector `n : SpinHalf.SpinSpace` selects the measured spin
observable `S(n) = ℏ_spin (n · σ) / 2`; the Pauli coordinates remain internal representation data.
The corresponding one-particle spin-1/2 observable lives in
`QuantumTheory.SpinfulLattice`. The measured spin current is

```text
J^(S(n)) = dΓ( 1/2 {v, S(n)} ),
```

transported to the bounded finite-lattice Hilbert realization. The source is an ordinary electric
bond current, so the response kernel is genuinely mixed:

```text
χᴿ_{J^(S(n)), J^charge_{u→v}}.
```

No equality between spin current and charge current is assumed. The conventional
current uses a supplied velocity. A separate spin-displacement channel uses
the position and Hamiltonian of the same finite hopping lattice, with
`D = dΓ({X,S}/2)`, `J = (i/ℏ)[H,D]`, geometric charge source `B` and
unit-source contact `(i/ℏ)[D,B]`. Its retarded kernel splits into conventional
and torque-dipole contributions. The equal-time displacement susceptibility
identifies its contact expectation. Conductivity normalization and bulk/DC
limits remain downstream. The finite global displacement derivative is not
identified with a locally conserved bulk current without further hypotheses.

The conventional/proper-current distinction is motivated by Shi, Zhang, Xiao,
and Niu, *Phys. Rev. Lett.* **96**, 076604 (2006),
[doi:10.1103/PhysRevLett.96.076604](https://doi.org/10.1103/PhysRevLett.96.076604).
Follow-ups are tracked in `docs/roadmaps/spin-hall.md`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse
open QuantumTheory.SpinfulLattice

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {Site : Type*} [Fintype Site]

variable [LinearOrder Site]

/-- With velocity fixed, the bounded spin-current observable is real-linear in the transported
spin-space component. -/
noncomputable def boundedSpinCurrentLinear
    (velocity : (SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ))
    (spinScale : ℝ) :
    QuantumTheory.SpinHalf.SpinSpace →ₗ[ℝ]
      (FiniteLatticeHilbertFock (SpinfulSite Site) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Site)) :=
  (((boundedOneBodyOperator (Site := SpinfulSite Site)).toLinearMap.comp
      (LinearMap.symmetrizedProductBilinear (K := ℂ)
        ((SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ)) velocity)).restrictScalars ℝ).comp
    (spinOneBodyLinear spinScale)

@[simp]
theorem boundedSpinCurrentLinear_apply
    (velocity : (SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ))
    (spinScale : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    boundedSpinCurrentLinear velocity spinScale spinComponent =
      boundedOneBodyOperator
        (LinearMap.symmetrizedProduct (K := ℂ) velocity (spinOneBodyLinear spinScale spinComponent)) :=
  rfl

/-- Neutral fixed-observable response channel for a finite spin current selected by a spin-space component vector and driven by an electric bond-current source. -/
noncomputable def boundedSpinCurrentBondSourceResponseChannel
    (velocity : (SpinfulSite Site →₀ ℂ) →ₗ[ℂ] (SpinfulSite Site →₀ ℂ))
    (spinScale : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace)
    (ℏ q : ℂ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (u v : SpinfulSite Site) :
    ResponseChannel (FiniteLatticeHilbertFock (SpinfulSite Site)) :=
  ResponseChannel.fixed
    (boundedSpinCurrentLinear velocity spinScale spinComponent)
    (boundedBondCurrent ℏ q K u v)


/-! ## Spin-displacement response to a uniform geometric Peierls source -/

/-- Proper spin-displacement/charge response on any finite spinful hopping
lattice. The contact coefficient includes the source profile at observation
time, as required by `ResponseChannel.observableVariation`. Set
`sourceValue = f t` for `causalResponse` with profile `f` at observation time
`t`, and `sourceValue = 1` for source-normalized frequency or Lehmann response.
Use free dynamics from the same hopping Hamiltonian and the same positive
physical hbar. The displacement is symmetrized before second quantization. -/
noncomputable def boundedSpinDisplacementDirectionalResponseChannel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (hbar q spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (sourceValue : ℝ) :
    ResponseChannel (FiniteLatticeHilbertFock (SpinfulSite Site)) :=
  let X := (spinfulGeometry geometry).directionalPosition measured
  let S := spinOneBodyLinear (Site := Site) spinScale component
  let D := LinearMap.symmetrizedProduct (K := ℂ) X S
  let B := boundedDirectionalCurrent (spinfulGeometry geometry) source
    (hbar : ℂ) (q : ℂ) K
  { measured := boundedOneBodyOperator
      (QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator D)
    source := B
    observableVariation := (sourceValue : ℂ) •
      (QuantumTheory.ConservationLaw.heisenbergScale hbar • ⁅-B, boundedOneBodyOperator D⁆) }

/-- At zero Peierls source the measured derivative is exactly the current
stored in the channel. Its first source derivative is the stored contact
for unit source profile; no independent contact observable is assumed. -/
theorem boundedSpinDisplacementDirectionalResponseChannel_peierls
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (hbar q spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace) :
    let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
      ((spinfulGeometry geometry).directionalPosition measured)
      (spinOneBodyLinear (Site := Site) spinScale component))
    let channel := boundedSpinDisplacementDirectionalResponseChannel
      geometry measured source K hbar q spinScale component 1
    let J := fun A : ℂ => QuantumTheory.ConservationLaw.heisenbergScale hbar •
      ⁅boundedDirectionalPeierlsHamiltonian (spinfulGeometry geometry) source
        (hbar : ℂ) (q : ℂ) K A, D⁆
    J 0 = channel.measured ∧ HasAlgebraicDerivAt J channel.observableVariation 0 := by
  let X := (spinfulGeometry geometry).directionalPosition measured
  let S := spinOneBodyLinear (Site := Site) spinScale component
  let D := LinearMap.symmetrizedProduct (K := ℂ) X S
  let c := QuantumTheory.ConservationLaw.heisenbergScale hbar
  let G := spinfulGeometry geometry
  let B := boundedDirectionalCurrent G source (hbar : ℂ) (q : ℂ) K
  change c • ⁅boundedDirectionalPeierlsHamiltonian G source
      (hbar : ℂ) (q : ℂ) K 0, boundedOneBodyOperator D⁆ =
    boundedOneBodyOperator (QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator D) ∧
    HasAlgebraicDerivAt
      (fun A => c • ⁅boundedDirectionalPeierlsHamiltonian G source
        (hbar : ℂ) (q : ℂ) K A, boundedOneBodyOperator D⁆)
      (((1 : ℝ) : ℂ) • (c • ⁅-B, boundedOneBodyOperator D⁆)) 0
  constructor
  · rw [boundedDirectionalPeierlsHamiltonian_zero]
    exact (QuantumTheory.ConservationLaw.map_heisenbergEvolution
      (boundedOneBodyOperator (Site := SpinfulSite Site)) hbar K.operator D).symm
  · rw [Complex.ofReal_one, one_smul]
    exact hasAlgebraicDerivAt_boundedDirectionalPeierlsHamiltonian_commutator_zero
      G source (hbar : ℂ) (q : ℂ) K c (boundedOneBodyOperator D)

/-- The explicit contact is precisely the equal-time boundary term of the
spin-displacement susceptibility, with the observation-time source factor.
No stationarity or differentiability of the time-evolution group is needed
for this algebraic identity. -/
theorem boundedSpinDisplacementDirectionalResponseChannel_contactExpectation
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (hbar q spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (sourceValue : ℝ)
    (U : Multiplicative ℝ →* unitary
      (FiniteLatticeHilbertFock (SpinfulSite Site) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Site)))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (t : ℝ) :
    let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
      ((spinfulGeometry geometry).directionalPosition measured)
      (spinOneBodyLinear (Site := Site) spinScale component))
    let channel := boundedSpinDisplacementDirectionalResponseChannel
      geometry measured source K hbar q spinScale component sourceValue
    channel.contactExpectation U expectation t =
      (sourceValue : ℂ) * retardedSusceptibility U hbar expectation D channel.source t t := by
  let D := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ)
    ((spinfulGeometry geometry).directionalPosition measured)
    (spinOneBodyLinear (Site := Site) spinScale component))
  let B := boundedDirectionalCurrent (spinfulGeometry geometry) source
    (hbar : ℂ) (q : ℂ) K
  exact retardedSusceptibility_sameTime_eq_commutatorVariation
    U hbar expectation D B (sourceValue : ℂ) t

/-- The real-space mixed retarded kernel splits into the conventional
spin-current and torque-dipole kernels without a separate position/velocity
hypothesis. Both terms couple to the same geometric charge source. -/
theorem boundedSpinDisplacementDirectionalResponseChannel_retardedKernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (hbar q spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (sourceValue : ℝ)
    (U : Multiplicative ℝ →* unitary
      (FiniteLatticeHilbertFock (SpinfulSite Site) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Site)))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (t s : ℝ) :
    let X := (spinfulGeometry geometry).directionalPosition measured
    let S := spinOneBodyLinear (Site := Site) spinScale component
    let v := QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator X
    let torque := QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator S
    let B := boundedDirectionalCurrent (spinfulGeometry geometry) source
      (hbar : ℂ) (q : ℂ) K
    (boundedSpinDisplacementDirectionalResponseChannel geometry measured source K
      hbar q spinScale component sourceValue).retardedKernel U hbar expectation t s =
      retardedSusceptibility U hbar expectation
        (boundedSpinCurrentLinear v spinScale component) B t s +
      retardedSusceptibility U hbar expectation
        (boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ) X torque)) B t s := by
  let X := (spinfulGeometry geometry).directionalPosition measured
  let S := spinOneBodyLinear (Site := Site) spinScale component
  let v := QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator X
  let torque := QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator S
  let B := boundedDirectionalCurrent (spinfulGeometry geometry) source
    (hbar : ℂ) (q : ℂ) K
  let J := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ) v S)
  let T := boundedOneBodyOperator (LinearMap.symmetrizedProduct (K := ℂ) X torque)
  change retardedSusceptibility U hbar expectation
    (boundedOneBodyOperator (QuantumTheory.ConservationLaw.heisenbergEvolution hbar K.operator
      (LinearMap.symmetrizedProduct (K := ℂ) X S))) B t s =
    retardedSusceptibility U hbar expectation J B t s +
      retardedSusceptibility U hbar expectation T B t s
  have hsplit : boundedOneBodyOperator (QuantumTheory.ConservationLaw.heisenbergEvolution
      hbar K.operator (LinearMap.symmetrizedProduct (K := ℂ) X S)) = J + T :=
    QuantumTheory.ConservationLaw.map_heisenbergEvolution_symmetrizedProduct
      (boundedOneBodyOperator (Site := SpinfulSite Site)).toLinearMap hbar K.operator X S
  rw [hsplit]
  exact (retardedSusceptibilityMeasuredLinearMap U hbar expectation B t s).map_add J T

end
end Transport
end Fermionic
end SecondQuantization

import LeanCondensedMatter.Models.RashbaExchange.FiniteMomentumSpinResponse
import LeanCondensedMatter.QuantumMechanics.SingleParticle.LocalizedTransport

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
  _root_.ConservationLaw.localizedQuantity (SpinfulSite Grid →₀ ℂ)
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
    heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (finiteRashbaMomentumSpinDisplacement spinScale component position) =
      QuantumMechanics.SingleParticle.heisenbergTransportFunctional
          (SpinfulSite Grid →₀ ℂ) hbar (finiteRashbaMomentumHamiltonian params momentum)
          LinearMap.id (spinOneBodyLinear spinScale component) position +
      QuantumMechanics.SingleParticle.heisenbergSourceFunctional
          (SpinfulSite Grid →₀ ℂ) hbar (finiteRashbaMomentumHamiltonian params momentum)
          LinearMap.id (spinOneBodyLinear spinScale component) position := by
  change heisenbergScale hbar •
      ⁅finiteRashbaMomentumHamiltonian params momentum,
        _root_.ConservationLaw.localizedQuantity (SpinfulSite Grid →₀ ℂ)
          LinearMap.id (spinOneBodyLinear spinScale component) position⁆ =
      heisenbergScale hbar •
        _root_.ConservationLaw.transportCommutator (SpinfulSite Grid →₀ ℂ)
          (finiteRashbaMomentumHamiltonian params momentum)
          LinearMap.id (spinOneBodyLinear spinScale component) position +
      heisenbergScale hbar •
        _root_.ConservationLaw.sourceCommutator (SpinfulSite Grid →₀ ℂ)
          (finiteRashbaMomentumHamiltonian params momentum)
          LinearMap.id (spinOneBodyLinear spinScale component) position
  rw [_root_.ConservationLaw.lie_localizedQuantity, smul_add]

/-- Heisenberg evolution of a spin displacement separates velocity-generated
spin transport from the explicitly nonconserved spin-torque contribution.
No position/velocity identification is assumed here. -/
theorem finiteRashbaMomentumSpinDisplacement_heisenberg_decomposition
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ)) :
    heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (finiteRashbaMomentumSpinDisplacement spinScale component position) =
      LinearMap.symmetrizedProduct
        (heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
          (finiteRashbaMomentumHamiltonian params momentum) position)
        (spinOneBodyLinear spinScale component) +
      LinearMap.symmetrizedProduct position
        (heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (spinOneBodyLinear spinScale component)) := by
  rw [finiteRashbaMomentumSpinDisplacement_balance]
  let H := finiteRashbaMomentumHamiltonian params momentum
  let S := spinOneBodyLinear (Site := Grid) spinScale component
  let c := heisenbergScale hbar
  change c • LinearMap.symmetrizedProduct ⁅H, position⁆ S +
      c • LinearMap.symmetrizedProduct position ⁅H, S⁆ =
    LinearMap.symmetrizedProduct (c • ⁅H, position⁆) S +
      LinearMap.symmetrizedProduct position (c • ⁅H, S⁆)
  have hleft :=
    ((LinearMap.symmetrizedProductRightLinear (SpinfulSite Grid →₀ ℂ) S).map_smul
      c ⁅H, position⁆).symm
  have hright :=
    ((LinearMap.symmetrizedProductLeftLinear (SpinfulSite Grid →₀ ℂ) position).map_smul
      c ⁅H, S⁆).symm
  simpa only [LinearMap.symmetrizedProductRightLinear_apply,
    LinearMap.symmetrizedProductLeftLinear_apply] using
    congrArg₂ (· + ·) hleft hright

/-- If an independently justified position representation has the *same*
Heisenberg velocity as the Rashba momentum derivative, the spin-displacement
derivative is conventional spin current plus the torque dipole. -/
theorem finiteRashbaMomentumSpinDisplacement_eq_spinCurrent_add_torque
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (direction : Fin 2)
    (position : (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ))
    (hvelocity :
      heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
        (finiteRashbaMomentumHamiltonian params momentum) position =
      finiteRashbaMomentumVelocity params momentum direction) :
    heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
        (finiteRashbaMomentumHamiltonian params momentum)
        (finiteRashbaMomentumSpinDisplacement spinScale component position) =
      LinearMap.symmetrizedProduct
        (finiteRashbaMomentumVelocity params momentum direction)
        (spinOneBodyLinear spinScale component) +
      LinearMap.symmetrizedProduct position
        (heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
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
      heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
        (finiteRashbaMomentumHamiltonian params momentum) position =
      finiteRashbaMomentumVelocity params momentum direction) :
    boundedOneBodyOperator
        (heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
          (finiteRashbaMomentumHamiltonian params momentum)
          (finiteRashbaMomentumSpinDisplacement spinScale component position)) =
      SecondQuantization.Fermionic.Transport.boundedSpinCurrentLinear
          (finiteRashbaMomentumVelocity params momentum direction)
          spinScale component +
        boundedOneBodyOperator
          (LinearMap.symmetrizedProduct position
            (heisenbergEvolution (SpinfulSite Grid →₀ ℂ) hbar
              (finiteRashbaMomentumHamiltonian params momentum)
              (spinOneBodyLinear spinScale component))) := by
  rw [finiteRashbaMomentumSpinDisplacement_eq_spinCurrent_add_torque
    params momentum hbar spinScale component direction position hvelocity]
  change boundedOneBodyOperator (_ + _) =
    boundedOneBodyOperator
        (LinearMap.symmetrizedProduct
          (finiteRashbaMomentumVelocity params momentum direction)
          (spinOneBodyLinear spinScale component)) +
      boundedOneBodyOperator _
  exact map_add (boundedOneBodyOperator (Site := SpinfulSite Grid)).toLinearMap _ _

end
end QuantumTheory.Models.RashbaExchange

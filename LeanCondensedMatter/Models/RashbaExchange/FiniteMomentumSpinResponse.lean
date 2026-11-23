import LeanCondensedMatter.Models.RashbaExchange.Model
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.SpinCurrentResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free

set_option linter.style.header false

/-!
# Finite Rashba momentum-grid spin/charge response on full fermionic Fock space

A finite index set supplies explicitly selected physical two-momenta. At each momentum the
one-particle Hamiltonian and in-plane velocity are the actual Rashba-exchange Pauli matrices.
Their block-diagonal direct sum acts on `SpinfulSite Grid`, whose mode type includes the spin
index. The standard finite-lattice second-quantization lift produces full-Fock operators;
the measured conventional spin current reuses `Fermionic.Transport.boundedSpinCurrentLinear`
and the electric source is the bounded lift of the signed charge velocity `q v_j`.

Unlike a real-space Peierls-bond source, the electric source in the momentum representation is
`q v_j`. The explicit first-order variation of the measured current is supplied independently.
This model is finite but does not derive a Ward identity, a stationary Gibbs state, a
nonzero transverse Kubo value, or the proper/torque-dipole current. A self-adjointness witness
for the block-diagonal full-Fock Hamiltonian is required when constructing its free dynamics.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.SpinfulLattice
open QuantumTheory.LinearResponse
open SecondQuantization.Fermionic.Lattice
open SecondQuantization.Fermionic.Transport

noncomputable section

variable {Grid : Type*} [LinearOrder Grid] [Fintype Grid]

/-- Direct sum of arbitrary internal 2×2 matrices over a finite momentum grid. The
operator is diagonal in the momentum label, but not necessarily in the spin index. -/
noncomputable def finiteMomentumBlockOneBody
    (blocks : Grid → InternalSpace.PauliMatrix) :
    (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ) :=
  ∑ k : Grid, ∑ a : Fin 2, ∑ b : Fin 2,
    blocks k a b • matrixUnit (spinfulSite k a) (spinfulSite k b)

/-- A finite grid of clean Rashba-exchange Hamiltonian blocks. -/
noncomputable def finiteRashbaMomentumHamiltonian
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ) :
    (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ) :=
  finiteMomentumBlockOneBody (fun k =>
    hamiltonian params (momentum k).1 (momentum k).2)

/-- Directional velocity obtained from the momentum derivative of the Rashba Hamiltonian,
with exactly the same finite momentum blocks as the Hamiltonian. -/
noncomputable def finiteRashbaMomentumVelocity
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (direction : Fin 2) :
    (SpinfulSite Grid →₀ ℂ) →ₗ[ℂ] (SpinfulSite Grid →₀ ℂ) :=
  finiteMomentumBlockOneBody (fun k =>
    velocityOperator params direction (momentum k).1 (momentum k).2)

/-- Finite-hopping presentation of the same block-diagonal Hamiltonian. The entire
finite set is an allowed incident set; this is not a claim of spatial locality. -/
noncomputable def finiteRashbaMomentumHopping
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ) :
    LocallyFiniteHopping (SpinfulSite Grid) where
  column := fun x => finiteRashbaMomentumHamiltonian params momentum (latticeKet x)
  incident := fun _ => Finset.univ
  self_mem := by intro x; simp
  outside_incident := by
    intro x y hy
    exact (hy (Finset.mem_univ y)).elim

/-- The full-Fock Hamiltonian of the sampled Rashba model, obtained with the
preexisting bounded fermionic second-quantization machinery. -/
noncomputable def finiteRashbaMomentumFockHamiltonian
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ) :
    FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
      FiniteLatticeHilbertFock (SpinfulSite Grid) :=
  boundedHoppingHamiltonian (finiteRashbaMomentumHopping params momentum)

/-- Finite-momentum spin/charge response channel: conventional spin current
`dΓ({v_i,S(n)}/2)`, signed electric source `dΓ(q v_j)`, and a supplied
observable-variation/contact operator. The contact is not silently set to zero. -/
noncomputable def finiteRashbaMomentumSpinChargeChannel
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (charge : ℂ)
    (observableVariation :
      FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Grid)) :
    ResponseChannel (FiniteLatticeHilbertFock (SpinfulSite Grid)) where
  measured :=
    boundedSpinCurrentLinear
      (finiteRashbaMomentumVelocity params momentum measured) spinScale component
  source :=
    boundedOneBodyOperator
      (charge • finiteRashbaMomentumVelocity params momentum source)
  observableVariation := observableVariation

/-- The measured current remains linear in the physical real spin-polarization vector.
The charge-driving vertex and observable variation are held fixed. -/
theorem finiteRashbaMomentumSpinChargeChannel_measured_add
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (spinScale : ℝ) (u v : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (charge : ℂ)
    (contact :
      FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Grid)) :
    (finiteRashbaMomentumSpinChargeChannel params momentum spinScale
      (u + v) measured source charge contact).measured =
      (finiteRashbaMomentumSpinChargeChannel params momentum spinScale
        u measured source charge contact).measured +
      (finiteRashbaMomentumSpinChargeChannel params momentum spinScale
        v measured source charge contact).measured := by
  change
    boundedSpinCurrentLinear (finiteRashbaMomentumVelocity params momentum measured)
        spinScale (u + v) =
      boundedSpinCurrentLinear (finiteRashbaMomentumVelocity params momentum measured)
        spinScale u +
      boundedSpinCurrentLinear (finiteRashbaMomentumVelocity params momentum measured)
        spinScale v
  exact map_add _ u v

/-- Conditional bounded free dynamics with the actual full-Fock Rashba Hamiltonian.
The self-adjointness bridge is kept as an explicit obligation, not assumed by the
finite momentum-grid construction alone. -/
noncomputable def finiteRashbaMomentumFreeSystem
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar)
    (hself : IsSelfAdjoint (finiteRashbaMomentumFockHamiltonian params momentum)) :
    BoundedFreeSystem (FiniteLatticeHilbertFock (SpinfulSite Grid)) where
  hamiltonian := ⟨finiteRashbaMomentumFockHamiltonian params momentum, hself⟩
  hbar := hbar
  hbar_pos := hhbar

/-- Exact causal Kubo kernel for the finite momentum-grid Fock response channel. -/
noncomputable def finiteRashbaMomentumSpinChargeRetardedKernel
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar)
    (hself : IsSelfAdjoint (finiteRashbaMomentumFockHamiltonian params momentum))
    (spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (charge : ℂ)
    (contact :
      FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Grid))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock (SpinfulSite Grid)))
    (t s : ℝ) : ℂ :=
  (finiteRashbaMomentumSpinChargeChannel params momentum spinScale component
    measured source charge contact).retardedKernel
      (freePropagatorGroup
        (finiteRashbaMomentumFreeSystem params momentum hbar hhbar hself))
      hbar expectation t s

/-- Exact finite-grid Kubo response is additive in the physical spin polarization, with
the same Hamiltonian, electric source, and expectation on all three terms. -/
theorem finiteRashbaMomentumSpinChargeRetardedKernel_add
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar)
    (hself : IsSelfAdjoint (finiteRashbaMomentumFockHamiltonian params momentum))
    (spinScale : ℝ) (u v : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (charge : ℂ)
    (contact :
      FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
        FiniteLatticeHilbertFock (SpinfulSite Grid))
    (expectation : NormalizedExpectation (FiniteLatticeHilbertFock (SpinfulSite Grid)))
    (t s : ℝ) :
    finiteRashbaMomentumSpinChargeRetardedKernel params momentum hbar hhbar hself
        spinScale (u + v) measured source charge contact expectation t s =
      finiteRashbaMomentumSpinChargeRetardedKernel params momentum hbar hhbar hself
        spinScale u measured source charge contact expectation t s +
      finiteRashbaMomentumSpinChargeRetardedKernel params momentum hbar hhbar hself
        spinScale v measured source charge contact expectation t s := by
  let U := freePropagatorGroup
    (finiteRashbaMomentumFreeSystem params momentum hbar hhbar hself)
  let J := boundedSpinCurrentLinear
    (finiteRashbaMomentumVelocity params momentum measured) spinScale
  let B := boundedOneBodyOperator
    (charge • finiteRashbaMomentumVelocity params momentum source)
  change retardedSusceptibility U hbar expectation (J (u + v)) B t s =
    retardedSusceptibility U hbar expectation (J u) B t s +
      retardedSusceptibility U hbar expectation (J v) B t s
  rw [map_add]
  exact (retardedSusceptibilityMeasuredLinearMap U hbar expectation B t s).map_add
    (J u) (J v)

end
end QuantumTheory.Models.RashbaExchange

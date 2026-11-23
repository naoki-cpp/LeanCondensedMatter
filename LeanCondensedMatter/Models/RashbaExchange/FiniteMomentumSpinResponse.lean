import LeanCondensedMatter.Models.RashbaExchange.Operator
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.SpinCurrentResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free

set_option linter.style.header false

/-!
# Finite Rashba momentum-grid spin/charge response on full fermionic Fock space

A finite index set supplies explicitly selected physical two-momenta. At each momentum the
one-particle Hamiltonian and in-plane velocity are the actual Rashba-exchange Pauli matrices.
Their block-diagonal direct sum acts on `SpinfulSite Grid`, whose mode type includes the spin
index. The canonical bounded one-body second-quantization lift produces full-Fock operators;
the measured conventional spin current reuses `Fermionic.Transport.boundedSpinCurrentLinear`
and the electric source is the bounded lift of the signed charge velocity `q v_j`.

Unlike a real-space Peierls-bond source, the electric source in the momentum representation is
`q v_j`. The explicit first-order variation of the measured current is supplied independently.
The assembled Fock Hamiltonian is self-adjoint because every Rashba block is Hermitian,
without an additional model-level Hermiticity assumption. This model is finite but does not
derive a Ward identity, a stationary Gibbs state, a nonzero transverse Kubo value, or the
proper/torque-dipole current.
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

/-- The canonical finite-Hilbert second quantization of block-diagonal
one-particle matrices expands into the same bounded matrix units. -/
theorem boundedFiniteMomentumBlockOneBody_eq_sum
    (blocks : Grid → InternalSpace.PauliMatrix) :
    boundedOneBodyOperator (finiteMomentumBlockOneBody blocks) =
      ∑ k : Grid, ∑ a : Fin 2, ∑ b : Fin 2,
        blocks k a b • boundedDgammaMatrixUnit (spinfulSite k a) (spinfulSite k b) := by
  simp only [finiteMomentumBlockOneBody, map_sum, map_smul,
    boundedOneBodyOperator_eq, boundedDgammaMatrixUnit]

/-- Hermitian momentum blocks yield a self-adjoint operator on the full finite
fermionic Fock space, by adjoint reversal of bounded matrix units. -/
theorem boundedFiniteMomentumBlockOneBody_selfAdjoint
    (blocks : Grid → InternalSpace.PauliMatrix)
    (hblocks : ∀ k, (blocks k).IsHermitian) :
    IsSelfAdjoint (boundedOneBodyOperator (finiteMomentumBlockOneBody blocks)) := by
  have hentry (k : Grid) (a b : Fin 2) :
      star (blocks k b a) = blocks k a b := by
    have h := congrArg (fun A : InternalSpace.PauliMatrix => A a b) (hblocks k).star_eq
    simpa [Matrix.conjTranspose_apply] using h
  rw [isSelfAdjoint_iff]
  simp only [boundedFiniteMomentumBlockOneBody_eq_sum,
    star_sum, star_smul, star_boundedDgammaMatrixUnit]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp_rw [hentry k]

/-- The full-Fock Rashba Hamiltonian is the direct second quantization of
its sampled one-body Hamiltonian; no artificial hopping representation is needed. -/
noncomputable def finiteRashbaMomentumFockHamiltonian
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ) :
    FiniteLatticeHilbertFock (SpinfulSite Grid) →L[ℂ]
      FiniteLatticeHilbertFock (SpinfulSite Grid) :=
  boundedOneBodyOperator (finiteRashbaMomentumHamiltonian params momentum)

/-- The sampled Rashba Hamiltonian is self-adjoint on the entire finite
Fock space, for arbitrary real Rashba, exchange, and mass parameters. -/
theorem finiteRashbaMomentumFockHamiltonian_selfAdjoint
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ) :
    IsSelfAdjoint (finiteRashbaMomentumFockHamiltonian params momentum) := by
  exact boundedFiniteMomentumBlockOneBody_selfAdjoint
    (fun k => hamiltonian params (momentum k).1 (momentum k).2)
    (fun k => hamiltonian_isHermitian params (momentum k).1 (momentum k).2)

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

/-- Bounded free dynamics from the directly second-quantized Rashba Hamiltonian,
using the proved self-adjointness of each momentum block. -/
noncomputable def finiteRashbaMomentumFreeSystem
    (params : HamiltonianParameters) (momentum : Grid → ℝ × ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar) :
    BoundedFreeSystem (FiniteLatticeHilbertFock (SpinfulSite Grid)) where
  hamiltonian := ⟨finiteRashbaMomentumFockHamiltonian params momentum,
    finiteRashbaMomentumFockHamiltonian_selfAdjoint params momentum⟩
  hbar := hbar
  hbar_pos := hhbar

end
end QuantumTheory.Models.RashbaExchange

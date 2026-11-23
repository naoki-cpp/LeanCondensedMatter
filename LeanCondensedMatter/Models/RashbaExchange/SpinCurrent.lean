import LeanCondensedMatter.Models.RashbaExchange.Current
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite two-level Rashba spin/charge response

At a fixed momentum the clean Rashba-exchange Hamiltonian acts on a two-level spin space.
A measured conventional spin current is the anticommutator
`J_i^(S(n)) = {v_i, S(n)}/2`, and the electric source is the signed charge vertex
`q v_j`. The spin direction is an arbitrary real spin-space vector.

For the out-of-plane spin component, the in-plane Rashba velocity term anticommutes
with `σ_z`. Consequently `J_i^(S_z) = (ℏ_spin/2) (p_i/m_eff) σ_z`.
At zero momentum the measured current, and hence its exact retarded Kubo response,
vanish even when the Rashba coupling and exchange splitting are nonzero.

This is a **single momentum-sector**, finite-dimensional response with a fixed measured
observable and no explicit source-dependent contact term. It is not a finite spinful
real-space Fock/lattice response, a proper-current/torque-dipole identification, or
a thermodynamic, zero-broadening, or finite-device spin Hall conductivity.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.LinearResponse

noncomputable section

/-- Conventional (not torque-dipole-completed) spin current at one Rashba momentum point.
The supplied polarization is a real spin-space vector, not a Pauli-axis label. -/
noncomputable def conventionalSpinCurrentMatrix
    (params : HamiltonianParameters) (direction : Fin 2)
    (px py spinScale : ℝ) (component : QuantumTheory.SpinHalf.SpinSpace) :
    InternalSpace.PauliMatrix :=
  (1 / 2 : ℂ) •
    (velocityOperator params direction px py *
        QuantumTheory.SpinHalf.spinMatrix spinScale component +
      QuantumTheory.SpinHalf.spinMatrix spinScale component *
        velocityOperator params direction px py)

/-- The Rashba spin-orbit term cancels from the conventional out-of-plane spin current:
`{v_i, S_z}/2 = (ℏ_spin/2)(p_i/m_eff) σ_z`.
This is an operator identity, not an assumption about the response. -/
theorem conventionalSpinCurrentMatrix_z_eq
    (params : HamiltonianParameters) (direction : Fin 2)
    (px py spinScale : ℝ) :
    conventionalSpinCurrentMatrix params direction px py spinScale
        (QuantumTheory.SpinHalf.cartesianBasisVector .z) =
      (((spinScale / 2 : ℝ) : ℂ) *
        (((if direction = 0 then px else py) / params.effectiveMass : ℝ) : ℂ)) •
        InternalSpace.pauliZ := by
  fin_cases direction <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [conventionalSpinCurrentMatrix,
      QuantumTheory.SpinHalf.spinMatrix_cartesianBasisVector,
      velocityOperator, InternalSpace.pauliBasis,
      InternalSpace.pauliX, InternalSpace.pauliY, InternalSpace.pauliZ,
      Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, smul_eq_mul] <;>
    ring

/-- At the momentum origin, the conventional z-polarized spin current vanishes
for either in-plane flow direction and arbitrary Rashba/exchange parameters. -/
theorem conventionalSpinCurrentMatrix_z_origin
    (params : HamiltonianParameters) (direction : Fin 2) (spinScale : ℝ) :
    conventionalSpinCurrentMatrix params direction 0 0 spinScale
      (QuantumTheory.SpinHalf.cartesianBasisVector .z) = 0 := by
  rw [conventionalSpinCurrentMatrix_z_eq]
  simp

/-- The actual clean two-level Rashba Hamiltonian with its positive time scale. -/
noncomputable def rashbaPointFreeSystem
    (params : Parameters) (px py : ℝ) (hparams : params.IsRegular) :
    BoundedFreeSystem (EuclideanSpace ℂ (Fin 2)) where
  hamiltonian := ⟨hamiltonianOperator params px py,
    hamiltonianOperator_isSelfAdjoint params px py⟩
  hbar := params.hbar
  hbar_pos := hparams.hbar_pos

/-- Finite two-level spin-current / charge-source cross-response channel.
The source is the charge-current vertex `q v_j`; the measured current is
`{v_i,S(n)}/2`. The observable is fixed under the source, so its contact
variation is zero by construction. -/
noncomputable def rashbaSpinChargePointChannel
    (params : Parameters) (spinScale : ℝ)
    (component : QuantumTheory.SpinHalf.SpinSpace)
    (measured source : Fin 2) (px py : ℝ) :
    ResponseChannel (EuclideanSpace ℂ (Fin 2)) :=
  ResponseChannel.fixed
    (matrixOperator (conventionalSpinCurrentMatrix params
      measured px py spinScale component))
    (currentBoundedOperator params source px py)

/-- At the momentum origin the channel's measured z-spin current is zero,
although the charge source can retain a nonzero Rashba vertex. -/
theorem rashbaSpinChargePointChannel_z_origin_measured
    (params : Parameters) (spinScale : ℝ) (measured source : Fin 2) :
    (rashbaSpinChargePointChannel params spinScale
      (QuantumTheory.SpinHalf.cartesianBasisVector .z)
      measured source 0 0).measured = 0 := by
  change matrixOperator
    (conventionalSpinCurrentMatrix params measured 0 0 spinScale
      (QuantumTheory.SpinHalf.cartesianBasisVector .z)) = 0
  rw [conventionalSpinCurrentMatrix_z_origin]
  simp [matrixOperator]

/-- A model-specific finite Kubo selection rule: the retarded z-spin / charge
response at the Rashba momentum origin is exactly zero for every normalized
expectation, positive ℏ, source direction, and pair of times. -/
theorem rashbaSpinChargePointChannel_z_origin_retardedKernel
    (params : Parameters) (hparams : params.IsRegular)
    (spinScale : ℝ) (measured source : Fin 2)
    (expectation : NormalizedExpectation (EuclideanSpace ℂ (Fin 2)))
    (t s : ℝ) :
    (rashbaSpinChargePointChannel params spinScale
      (QuantumTheory.SpinHalf.cartesianBasisVector .z)
      measured source 0 0).retardedKernel
      (freePropagatorGroup (rashbaPointFreeSystem params 0 0 hparams))
      params.hbar expectation t s = 0 := by
  simp only [ResponseChannel.retardedKernel,
    rashbaSpinChargePointChannel_z_origin_measured]
  by_cases h : s ≤ t
  · simp [retardedSusceptibility, commutatorSusceptibility,
      heisenbergEvolution_apply, LieRing.of_associative_ring_bracket, h]
  · simp [retardedSusceptibility, h]

end
end QuantumTheory.Models.RashbaExchange

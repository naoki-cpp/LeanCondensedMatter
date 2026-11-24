import LeanCondensedMatter.Models.RashbaExchange.Model
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Finite momentum-block obstruction to Rashba position/velocity identification

For a single two-component Rashba momentum block, the trace of every
finite-dimensional commutator vanishes by cyclicity. However the velocity
vertex `∂H(p)/∂p_i` has trace `2 p_i / m_eff`. At nonzero `p_i / m_eff`,
there is therefore no 2×2 matrix `X_i(p)` satisfying
`(i/ℏ)[H(p),X_i(p)] = ∂H(p)/∂p_i`.

This is a *single momentum block* obstruction. It does not rule out a
non-diagonal operator mixing momentum sectors, a real-space lattice position,
or a momentum derivative on a suitable function space. It shows why the
position/velocity hypothesis of `SpinDisplacementBridge` cannot simply be
discharged by a pointwise 2×2 position matrix.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

/-- The spin-orbit (Pauli) part is traceless. The velocity trace only sees
the scalar parabolic dispersion for either in-plane direction. -/
theorem trace_velocityOperator
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) :
    Matrix.trace (velocityOperator params direction px py) =
      (2 : ℂ) * (((if direction = 0 then px / params.effectiveMass
        else py / params.effectiveMass : ℝ)) : ℂ) := by
  fin_cases direction
  · simp [velocityOperator, Matrix.trace, Fin.sum_univ_two,
      InternalSpace.pauliY]
  · simp [velocityOperator, Matrix.trace, Fin.sum_univ_two,
      InternalSpace.pauliX]
    ring

/-- A nonzero parabolic velocity component gives a nonzero finite matrix trace. -/
theorem trace_velocityOperator_ne_zero
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ)
    (hmomentum :
      (if direction = 0 then px / params.effectiveMass
        else py / params.effectiveMass) ≠ 0) :
    Matrix.trace (velocityOperator params direction px py) ≠ 0 := by
  rw [trace_velocityOperator]
  apply mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  exact_mod_cast hmomentum

/-- No finite 2×2 pointwise position matrix can realize Rashba's velocity
as the Heisenberg commutator at nonzero parabolic velocity. The proof does
not assume the candidate position matrix is diagonal or self-adjoint. -/
theorem no_pointwise_rashba_position_of_nonzero_parabolic_velocity
    (params : HamiltonianParameters) (direction : Fin 2) (px py hbar : ℝ)
    (hmomentum :
      (if direction = 0 then px / params.effectiveMass
        else py / params.effectiveMass) ≠ 0)
    (position : InternalSpace.PauliMatrix) :
    (Complex.I / (hbar : ℂ)) •
      (hamiltonian params px py * position - position * hamiltonian params px py) ≠
        velocityOperator params direction px py := by
  intro hposition
  have hcomm :
      Matrix.trace
        (hamiltonian params px py * position -
          position * hamiltonian params px py) = 0 := by
    rw [Matrix.trace_sub,
      Matrix.trace_mul_comm (hamiltonian params px py) position, sub_self]
  have hzero :
      Matrix.trace
        ((Complex.I / (hbar : ℂ)) •
          (hamiltonian params px py * position -
            position * hamiltonian params px py)) = 0 := by
    rw [Matrix.trace_smul, hcomm]
    simp
  have hvelocity : Matrix.trace (velocityOperator params direction px py) = 0 :=
    hposition.symm ▸ hzero
  exact (trace_velocityOperator_ne_zero params direction px py hmomentum) hvelocity

end
end QuantumTheory.Models.RashbaExchange

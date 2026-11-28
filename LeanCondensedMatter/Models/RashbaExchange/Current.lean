import LeanCondensedMatter.Models.RashbaExchange.Model.OperatorSpectral
import LeanCondensedMatter.QuantumTheory.TwoBand
import LeanCondensedMatter.Models.RashbaExchange.Model
import LeanCondensedMatter.Transport.Core.FiniteResponseParameters
import LeanCondensedMatter.Analysis.Operator.FiniteTrace

set_option linter.style.header false

/-!
# Charge-current operators and spectral current blocks of the Rashba-exchange model

The Hamiltonian, velocity operators, and band projectors are defined using clean
`HamiltonianParameters` upstream. This module owns the finite-response parameter bundle and
momentum disk, and attaches the signed carrier charge from
`Parameters` to the matrix and bounded current vertices, and forms the ordered
current-projector trace used by the Bastin/Berry response.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open ContinuousLinearMap
open QuantumTheory.Transport

/-- Clean Hamiltonian parameters together with the common finite continuum response data. -/
structure Parameters extends HamiltonianParameters, QuantumTheory.Transport.FiniteResponseParameters

/-- Retain only the clean Hamiltonian data. -/
instance : Coe Parameters HamiltonianParameters where
  coe params := params.toHamiltonianParameters

/-- Regular finite-response parameters, including positive effective mass. -/
structure Parameters.IsRegular (params : Parameters) : Prop
    extends QuantumTheory.Transport.FiniteResponseParameters.IsRegular params.toFiniteResponseParameters where
  effectiveMass_pos : 0 < params.effectiveMass

/-- Membership in the finite closed momentum disk. -/
def inMomentumDomain (params : Parameters) (px py : ℝ) : Prop :=
  px ^ 2 + py ^ 2 ≤ params.momentumCutoff ^ 2

/-- Charge-current matrix operator in the convention j_i = q v_i. -/
def currentOperator (params : Parameters) (direction : Fin 2) (px py : ℝ) : InternalSpace.PauliMatrix :=
  (((params.signedCharge : ℝ) : ℂ)) • velocityOperator params direction px py

/-- Bounded charge-current operator consumed by response kernels. -/
noncomputable def currentBoundedOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (currentOperator params direction px py)

@[simp] theorem currentBoundedOperator_eq_charge_smul_velocity
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    currentBoundedOperator params direction px py =
      (((params.signedCharge : ℝ) : ℂ)) •
        velocityBoundedOperator params direction px py := by
  unfold currentBoundedOperator velocityBoundedOperator currentOperator matrixOperator
  rw [map_smul]

/-- When the Rashba coupling vanishes, each in-plane charge-current vertex is a scalar multiple of
the identity. This is the operator-level degeneracy used by the Hall-response zero theorem. -/
theorem currentBoundedOperator_rashba_zero
    (params : Parameters) (direction : Fin 2) (px py : ℝ)
    (hAlpha : params.rashbaVelocity = 0) :
    currentBoundedOperator params direction px py =
      (((params.signedCharge *
        (if direction = 0 then px / params.effectiveMass else py / params.effectiveMass) : ℝ) : ℂ)) •
        (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  fin_cases direction <;>
    simp [currentBoundedOperator, currentOperator, velocityOperator, matrixOperator, hAlpha,
      smul_smul]

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)`. -/
noncomputable def currentBandBlockTrace
    (params : Parameters) (μ ν : Fin 2) (source target : TwoBand) (px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator params target px py *
      currentBoundedOperator params μ px py *
      bandProjectorOperator params source px py *
      currentBoundedOperator params ν px py)

/-- Cyclicity of finite-dimensional trace exchanges the current directions
and swaps the ordered band projectors, without complex conjugation. -/
theorem currentBandBlockTrace_swap
    (params : Parameters) (μ ν : Fin 2) (source target : TwoBand)
    (px py : ℝ) :
    currentBandBlockTrace params ν μ source target px py =
      currentBandBlockTrace params μ ν target source px py := by
  unfold currentBandBlockTrace
  simpa only [mul_assoc] using
    (finiteDimensionalOperatorTrace_mul_comm
      (bandProjectorOperator params target px py *
        currentBoundedOperator params ν px py)
      (bandProjectorOperator params source px py *
        currentBoundedOperator params μ px py))

end
end QuantumTheory.Models.RashbaExchange

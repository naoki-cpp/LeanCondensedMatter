import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.ConservationLaws
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-dimensional Kubo–Onsager reciprocity from time reversal

The input is an operator-level, conjugate-linear time-reversal action on
bounded observables. Hamiltonians, density operators, currents, and contact
operators are transformed as physical operators. In particular there is
no same-label pairing of energy eigenvectors. The induced action on
observables can be involutive even if the antiunitary on state vectors
has square minus the identity.

The ordinary finite trace gives the physical equilibrium expectation.
Kubo reciprocity is derived from antiunitary conjugation of correlations,
stationarity of the density matrix, and Hermiticity of the currents.
No DC, infinite-time, or thermodynamic limit is claimed.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse
open ContinuousLinearMap

noncomputable section

/-- Finite-dimensional data for microscopic time reversal.

The conjugate-linear multiplicative operator action models conjugation by
an antiunitary on state vectors. Its exponential and trace transformation
laws are recorded explicitly. They are algebraic/analytic properties of
that action, not assumptions about any response or conductivity tensor.

The equilibrium state commutes with the Hamiltonian. Current operators
are odd under reversal, whereas the explicit contact operator is even,
with the measured/source direction indices exchanged. -/
structure KuboTimeReversalData (M d H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] where
  reverse : M → M
  system : M → BoundedFreeSystem H
  hbar : ℝ
  system_hbar : ∀ m, (system m).hbar = hbar
  density : M → DensityOperator H
  density_stationary : ∀ m, Commute (system m).hamiltonian.1 (density m).op
  transform : (H →L[ℂ] H) → (H →L[ℂ] H)
  transform_add : ∀ A B, transform (A + B) = transform A + transform B
  transform_mul : ∀ A B, transform (A * B) = transform A * transform B
  transform_star : ∀ A, transform (star A) = star (transform A)
  transform_smul : ∀ (c : ℂ) A, transform (c • A) = (star c) • transform A
  transform_exp : ∀ A, transform (NormedSpace.exp A) = NormedSpace.exp (transform A)
  transform_trace : ∀ A,
    finiteDimensionalOperatorTrace (transform A) =
      star (finiteDimensionalOperatorTrace A)
  hamiltonian_reverse : ∀ m,
    transform (system m).hamiltonian.1 =
      (system (reverse m)).hamiltonian.1
  density_reverse : ∀ m,
    transform (density m).op = (density (reverse m)).op
  current : M → d → (H →L[ℂ] H)
  current_selfAdjoint : ∀ m i, IsSelfAdjoint (current m i)
  current_reverse : ∀ m i, transform (current m i) = -(current (reverse m) i)
  contact : M → d → d → (H →L[ℂ] H)
  contact_selfAdjoint : ∀ m i j, IsSelfAdjoint (contact m i j)
  contact_reverse : ∀ m i j,
    transform (contact m i j) = contact (reverse m) j i

namespace KuboTimeReversalData

variable {M d H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [FiniteDimensional ℂ H]
variable (data : KuboTimeReversalData M d H)

/-- The finite-dimensional equilibrium expectation, with no chosen eigenbasis. -/
noncomputable def expectation (m : M) (A : H →L[ℂ] H) : ℂ :=
  finiteDimensionalOperatorTrace ((data.density m).op * A)

/-- Reality of equilibrium expectations of adjoints follows from the
self-adjoint density operator and cyclicity of the finite trace. -/
theorem expectation_star (m : M) (A : H →L[ℂ] H) :
    data.expectation m (star A) = star (data.expectation m A) := by
  unfold expectation
  calc
    finiteDimensionalOperatorTrace ((data.density m).op * star A) =
        finiteDimensionalOperatorTrace (star A * (data.density m).op) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace (star ((data.density m).op * A)) := by
      simp only [star_mul, ContinuousLinearMap.star_eq_adjoint,
        (data.density m).isSelfAdjoint.adjoint_eq]
    _ = star (finiteDimensionalOperatorTrace ((data.density m).op * A)) :=
      finiteDimensionalOperatorTrace_star _

/-- Microscopic density covariance and the conjugate-linearity of the
finite trace imply the transformation law for arbitrary expectations. -/
theorem expectation_reverse (m : M) (A : H →L[ℂ] H) :
    data.expectation (data.reverse m) (data.transform A) =
      star (data.expectation m A) := by
  unfold expectation
  calc
    finiteDimensionalOperatorTrace ((data.density (data.reverse m)).op * data.transform A) =
        finiteDimensionalOperatorTrace
          (data.transform (data.density m).op * data.transform A) := by
      rw [data.density_reverse m]
    _ = finiteDimensionalOperatorTrace
          (data.transform ((data.density m).op * A)) := by
      rw [data.transform_mul]
    _ = star (finiteDimensionalOperatorTrace ((data.density m).op * A)) :=
      data.transform_trace _

end KuboTimeReversalData

end
end QuantumTheory.Transport

import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.ConservationLaws
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary.Trace

set_option linter.style.header false

/-!
# Microscopic operator time-reversal data for transport

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

The operator action is constructed from an actual Hilbert-space
antiunitary. Its multiplicativity, conjugate-linearity, exponential
covariance and trace conjugation follow from separately proved theorems,
not additional assumptions about the response or conductivity tensor.

The equilibrium state commutes with the Hamiltonian. Current operators
are odd under reversal, whereas the explicit contact operator is even,
with the measured/source direction indices exchanged. -/
structure KuboTimeReversalData (M d H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] where
  /-- Reversal of the time-reversal-odd control parameters. -/
  reverse : M → M
  /-- Bounded Hamiltonian and free evolution at each control parameter. -/
  system : M → BoundedFreeSystem H
  /-- Common reduced Planck constant across the parameter family. -/
  hbar : ℝ
  system_hbar : ∀ m, (system m).hbar = hbar
  /-- Positive normalized equilibrium density operator. -/
  density : M → DensityOperator H
  density_stationary : ∀ m, Commute (system m).hamiltonian.1 (density m).op
  /-- Microscopic antiunitary on Hilbert-space vectors; no square constraint. -/
  timeReversal : AntiunitaryMap H
  hamiltonian_reverse : ∀ m,
    timeReversal.conjugateOperator (system m).hamiltonian.1 =
      (system (reverse m)).hamiltonian.1
  density_reverse : ∀ m,
    timeReversal.conjugateOperator (density m).op = (density (reverse m)).op
  /-- Measured and source charge-current operators, indexed by direction. -/
  current : M → d → Observable H
  current_reverse : ∀ m i,
    timeReversal.conjugateOperator (current m i).1 = -(current (reverse m) i).1
  /-- Explicit observable-variation/contact operator for each ordered direction pair. -/
  contact : M → d → d → Observable H
  contact_reverse : ∀ m i j,
    timeReversal.conjugateOperator (contact m i j).1 = (contact (reverse m) j i).1

namespace KuboTimeReversalData

variable {M d H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [FiniteDimensional ℂ H]
variable (data : KuboTimeReversalData M d H)

/-- Microscopic density covariance and the conjugate-linearity of the
finite trace imply the transformation law for arbitrary expectations. -/
theorem expectation_reverse (m : M) (A : H →L[ℂ] H) :
    (data.density (data.reverse m)).expectation (data.timeReversal.conjugateOperator A) =
      star ((data.density m).expectation A) := by
  rw [(data.density (data.reverse m)).expectation_eq_finiteDimensionalOperatorTrace,
    (data.density m).expectation_eq_finiteDimensionalOperatorTrace]
  calc
    finiteDimensionalOperatorTrace ((data.density (data.reverse m)).op * data.timeReversal.conjugateOperator A) =
        finiteDimensionalOperatorTrace
          (data.timeReversal.conjugateOperator (data.density m).op * data.timeReversal.conjugateOperator A) := by
      rw [data.density_reverse m]
    _ = finiteDimensionalOperatorTrace
          (data.timeReversal.conjugateOperator ((data.density m).op * A)) := by
      exact (congrArg finiteDimensionalOperatorTrace
        (data.timeReversal.conjugateOperator_mul (data.density m).op A)).symm
    _ = star (finiteDimensionalOperatorTrace ((data.density m).op * A)) :=
      data.timeReversal.conjugateOperator_trace _

end KuboTimeReversalData

end
end QuantumTheory.Transport

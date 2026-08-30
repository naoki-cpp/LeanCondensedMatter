import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import LeanCondensedMatter.Transport.Streda.OperatorKernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-dimensional trace kernels for the regularized Středa split

The operator-valued kernels in `Streda.OperatorKernel` become the scalar energy kernels used by a
finite Kubo–Bastin formula only after applying the ordinary finite-dimensional trace owned by
`Analysis.Operator.FiniteTrace`. This module applies that generic trace primitive to the Středa
operator kernels and proves that:

* differentiation of the real-energy Středa operator path descends through the trace;
* the traced surface primitive has the traced operator derivative;
* the residual sea trace is antisymmetric under exchanging the two current vertices;
* the canonical traced derivative and residual sea kernels are continuous at positive broadening;
  and
* the operator pointwise Bastin decomposition descends to scalar trace kernels.

No occupation integral or identification with the finite-frequency response from the field layer
is made here. Zero broadening, DC, disorder, trace per unit volume, magnetic derivatives, and the
thermodynamic limit remain outside this module.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Scalar trace of the regularized Středa surface primitive. -/
noncomputable def regularizedStredaSurfacePrimitiveTrace
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedStredaSurfacePrimitiveOperator
      hamiltonian current₁ current₂ energy broadening)

/-- Scalar trace of the exact derivative of the regularized Středa surface primitive. -/
noncomputable def regularizedStredaSurfacePrimitiveTraceDerivative
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedStredaSurfacePrimitiveOperatorDerivative
      hamiltonian current₁ current₂ energy broadening)

/-- Scalar ordinary-trace form of the canonical static regularized Bastin integrand. -/
noncomputable def regularizedBastinTraceIntegrand
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedBastinOperatorIntegrand
      hamiltonian current₁ current₂ energy broadening)

/-- Scalar ordinary-trace form of the finite-broadening residual sea kernel. -/
noncomputable def regularizedStredaResidualSeaTraceKernel
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace (H := H)
    (regularizedStredaResidualSeaOperatorKernel
      hamiltonian current₁ current₂ energy broadening)

/-- The finite-broadening residual sea trace is antisymmetric under exchange of the two current
vertices. This is an exact finite-dimensional trace-cyclicity identity. -/
theorem regularizedStredaResidualSeaTraceKernel_swap
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) :
    regularizedStredaResidualSeaTraceKernel
        hamiltonian current₁ current₂ energy broadening =
      -regularizedStredaResidualSeaTraceKernel
        hamiltonian current₂ current₁ energy broadening := by
  let R : H →L[ℂ] H := retardedResolvent hamiltonian energy broadening
  let A : H →L[ℂ] H := advancedResolvent hamiltonian energy broadening
  have hres : ∀ X Y : H →L[ℂ] H,
      regularizedStredaResidualSeaOperatorKernel
          hamiltonian X Y energy broadening =
        (1 / 2 : ℂ) •
          (-(X * R * Y * R ^ 2) + X * R * Y * A ^ 2 +
            Y * A * X * R ^ 2 - Y * A * X * A ^ 2 +
            X * R ^ 2 * Y * R - X * R ^ 2 * Y * A -
            Y * A ^ 2 * X * R + Y * A ^ 2 * X * A) := by
    intro X Y
    dsimp [R, A]
    unfold regularizedStredaResidualSeaOperatorKernel
      regularizedBastinOperatorIntegrand
      regularizedStredaSurfacePrimitiveOperatorDerivative
      smrckaStredaSurfaceFactorDerivative
      retardedAdvancedResolventDifference
      retardedAdvancedResolventDifferenceDerivative
    noncomm_ring
  have hRR₁ :
      finiteDimensionalOperatorTrace (H := H) (current₂ * R ^ 2 * current₁ * R) =
        finiteDimensionalOperatorTrace (H := H) (current₁ * R * current₂ * R ^ 2) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₂ * R ^ 2) (current₁ * R))
  have hRR₂ :
      finiteDimensionalOperatorTrace (H := H) (current₂ * R * current₁ * R ^ 2) =
        finiteDimensionalOperatorTrace (H := H) (current₁ * R ^ 2 * current₂ * R) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₂ * R) (current₁ * R ^ 2))
  have hAA₁ :
      finiteDimensionalOperatorTrace (H := H) (current₂ * A * current₁ * A ^ 2) =
        finiteDimensionalOperatorTrace (H := H) (current₁ * A ^ 2 * current₂ * A) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₂ * A) (current₁ * A ^ 2))
  have hAA₂ :
      finiteDimensionalOperatorTrace (H := H) (current₂ * A ^ 2 * current₁ * A) =
        finiteDimensionalOperatorTrace (H := H) (current₁ * A * current₂ * A ^ 2) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₂ * A ^ 2) (current₁ * A))
  have hRA₁ :
      finiteDimensionalOperatorTrace (H := H) (current₁ * R * current₂ * A ^ 2) =
        finiteDimensionalOperatorTrace (H := H) (current₂ * A ^ 2 * current₁ * R) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₁ * R) (current₂ * A ^ 2))
  have hRA₂ :
      finiteDimensionalOperatorTrace (H := H) (current₂ * A * current₁ * R ^ 2) =
        finiteDimensionalOperatorTrace (H := H) (current₁ * R ^ 2 * current₂ * A) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₂ * A) (current₁ * R ^ 2))
  have hRA₃ :
      finiteDimensionalOperatorTrace (H := H) (current₂ * R * current₁ * A ^ 2) =
        finiteDimensionalOperatorTrace (H := H) (current₁ * A ^ 2 * current₂ * R) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₂ * R) (current₁ * A ^ 2))
  have hRA₄ :
      finiteDimensionalOperatorTrace (H := H) (current₁ * A * current₂ * R ^ 2) =
        finiteDimensionalOperatorTrace (H := H) (current₂ * R ^ 2 * current₁ * A) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current₁ * A) (current₂ * R ^ 2))
  unfold regularizedStredaResidualSeaTraceKernel
  rw [hres current₁ current₂, hres current₂ current₁]
  simp only [map_smul, map_add, map_sub, map_neg]
  rw [hRR₁, hRR₂, hAA₁, hAA₂, hRA₁, hRA₂, hRA₃, hRA₄]
  ring

/-- The traced surface primitive has the traced operator derivative at every positive broadening. -/
theorem hasDerivAt_regularizedStredaSurfacePrimitiveTrace
    [CompleteSpace H]
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt
      (fun x : ℝ => regularizedStredaSurfacePrimitiveTrace
        hamiltonian current₁ current₂ x broadening)
      (regularizedStredaSurfacePrimitiveTraceDerivative
        hamiltonian current₁ current₂ energy broadening)
      energy := by
  unfold regularizedStredaSurfacePrimitiveTrace
    regularizedStredaSurfacePrimitiveTraceDerivative
  exact hasDerivAt_finiteDimensionalOperatorTrace_comp
    (hasDerivAt_regularizedStredaSurfacePrimitiveOperator
      hamiltonian hself current₁ current₂ energy broadening hbroadening)

/-- At fixed positive broadening, the traced surface-primitive derivative is continuous in energy. -/
theorem continuous_regularizedStredaSurfacePrimitiveTraceDerivative_energy
    [CompleteSpace H]
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      regularizedStredaSurfacePrimitiveTraceDerivative
        hamiltonian current₁ current₂ energy broadening) := by
  unfold regularizedStredaSurfacePrimitiveTraceDerivative
  exact (finiteDimensionalOperatorTrace (H := H)).continuous.comp
    (continuous_regularizedStredaSurfacePrimitiveOperatorDerivative_energy
      hamiltonian hself current₁ current₂ broadening hbroadening)

/-- At fixed positive broadening, the traced residual sea kernel is continuous in energy. -/
theorem continuous_regularizedStredaResidualSeaTraceKernel_energy
    [CompleteSpace H]
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ =>
      regularizedStredaResidualSeaTraceKernel
        hamiltonian current₁ current₂ energy broadening) := by
  unfold regularizedStredaResidualSeaTraceKernel
  exact (finiteDimensionalOperatorTrace (H := H)).continuous.comp
    (continuous_regularizedStredaResidualSeaOperatorKernel_energy
      hamiltonian hself current₁ current₂ broadening hbroadening)

/-- The pointwise operator decomposition descends to the ordinary finite-dimensional trace. -/
theorem regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        hamiltonian current₁ current₂ energy broadening =
      regularizedStredaSurfacePrimitiveTraceDerivative
          hamiltonian current₁ current₂ energy broadening +
        regularizedStredaResidualSeaTraceKernel
          hamiltonian current₁ current₂ energy broadening := by
  unfold regularizedBastinTraceIntegrand
    regularizedStredaSurfacePrimitiveTraceDerivative
    regularizedStredaResidualSeaTraceKernel
  rw [regularizedBastinOperatorIntegrand_eq_surfaceDerivative_add_residualSea]
  exact map_add (finiteDimensionalOperatorTrace (H := H)) _ _

end

end QuantumTheory.Transport

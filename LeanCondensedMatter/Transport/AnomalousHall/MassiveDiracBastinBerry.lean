import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSpectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerryBridge
import LeanCondensedMatter.Transport.StredaTraceKernel

set_option linter.style.header false

/-!
# Massive-Dirac Bastin projector blocks and Berry curvature

The finite-broadening Kubo–Bastin layer and the clean Berry-curvature layer now share the same
massive-Dirac spectral projectors.  This file makes that common block explicit without choosing an
eigenvector gauge.

First, the generic retarded/advanced resolvents in the Bastin integrand are replaced by the exact
projector resolvents proved in `MassiveDiracStredaSpectral`.  Second, the interband operator trace

```text
Tr(P_m jₓ P_n jᵧ),  m = oppositeBand n,
```

is transported back to the concrete `2 × 2` matrix trace.  Since `j_i = -e v_i`, this trace is
`e²` times the force-matrix numerator already used in `MassiveDiracBerryBridge`.  Dividing its
imaginary part by the squared interband gap therefore reproduces `e² Ω_n`.

This is still a pointwise, finite-dimensional bridge.  The next step is to expand the full Bastin
projector expression into its diagonal/interband band blocks and then perform the occupation and
zero-broadening analysis.  No such limiting statement is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The charge-current matrix is the velocity matrix multiplied by the electron charge `-e`. -/
theorem currentX_eq_charge_smul_velocityX (e v : ℝ) :
    currentX e v = (((-e : ℝ) : ℂ)) • velocityX v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [currentX, velocityX, sigmaX]

/-- The `y` charge-current matrix is likewise `-e` times the velocity matrix. -/
theorem currentY_eq_charge_smul_velocityY (e v : ℝ) :
    currentY e v = (((-e : ℝ) : ℂ)) • velocityY v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [currentY, velocityY, sigmaY]

/-- Gauge-independent interband current block in the bounded-operator representation. -/
noncomputable def interbandCurrentTrace
    (band : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator (oppositeBand band) v m px py * currentXOperator e v *
      bandProjectorOperator band v m px py * currentYOperator e v)

/-- The bounded-operator interband current trace is exactly the ordinary matrix trace of the same
projector/current block. -/
theorem interbandCurrentTrace_eq_matrixTrace
    (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace band e v m px py =
      Matrix.trace
        (bandProjector (oppositeBand band) v m px py * currentX e v *
          bandProjector band v m px py * currentY e v) := by
  unfold interbandCurrentTrace
  simpa [bandProjectorOperator, currentXOperator, currentYOperator, matrixOperator] using
    finiteDimensionalOperatorTrace_matrixOperator
      (bandProjector (oppositeBand band) v m px py * currentX e v *
        bandProjector band v m px py * currentY e v)

/-- Replacing each charge current by `-e` times the corresponding velocity pulls out `e²` from
the interband projector trace. -/
theorem matrixInterbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    (band : Band) (e v m px py : ℝ) :
    Matrix.trace
        (bandProjector (oppositeBand band) v m px py * currentX e v *
          bandProjector band v m px py * currentY e v) =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator band v m px py := by
  rw [currentX_eq_charge_smul_velocityX, currentY_eq_charge_smul_velocityY]
  simp [forceMatrixTraceNumerator]
  ring

/-- Operator form of the same `e²` factorization. -/
theorem interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace band e v m px py =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator band v m px py := by
  rw [interbandCurrentTrace_eq_matrixTrace]
  exact matrixInterbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    band e v m px py

/-- Imaginary part of the physical-current interband block. -/
theorem interbandCurrentTrace_im
    (band : Band) (e v m px py : ℝ) :
    (interbandCurrentTrace band e v m px py).im =
      e ^ 2 * (forceMatrixTraceNumerator band v m px py).im := by
  rw [interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator]
  push_cast
  simp [Complex.mul_im, pow_two]

/-- Berry-curvature combination formed directly from the physical-current interband trace. -/
noncomputable def interbandCurrentBerryWeight
    (band : Band) (e v m px py : ℝ) : ℝ :=
  2 * (interbandCurrentTrace band e v m px py).im /
    interbandEnergyGap band v m px py ^ 2

/-- The current-current interband block is `e²` times the force-matrix Berry-curvature block. -/
theorem interbandCurrentBerryWeight_eq_chargeSq_forceMatrixBerryCurvature
    (band : Band) (e v m px py : ℝ) :
    interbandCurrentBerryWeight band e v m px py =
      e ^ 2 * forceMatrixBerryCurvature band v m px py := by
  rw [interbandCurrentBerryWeight, interbandCurrentTrace_im]
  unfold forceMatrixBerryCurvature
  ring

/-- Away from the Dirac degeneracy, the physical-current interband block therefore reproduces
`e²` times the clean Berry curvature. -/
theorem interbandCurrentBerryWeight_eq_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    interbandCurrentBerryWeight band e v m px py =
      e ^ 2 * berryCurvature band v m px py := by
  rw [interbandCurrentBerryWeight_eq_chargeSq_forceMatrixBerryCurvature]
  rw [forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE]

/-- Bastin operator integrand with the generic Green operators replaced by their exact massive-Dirac
projector expansions. -/
noncomputable def projectorBastinOperatorIntegrand
    (e v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let retarded :=
    projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py
  let advanced :=
    projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py
  (currentXOperator e v * retarded ^ 2 * currentYOperator e v -
      currentYOperator e v * advanced ^ 2 * currentXOperator e v) *
    (retarded - advanced)

/-- Ordinary trace of the projector-expanded Bastin operator kernel. -/
noncomputable def projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (projectorBastinOperatorIntegrand e v m px py probeEnergy broadening)

/-- At positive broadening and away from the band degeneracy, the generic massive-Dirac Bastin trace
integrand is exactly the projector-expanded expression. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentXOperator e v) (currentYOperator e v) probeEnergy broadening =
      projectorBastinTraceIntegrand e v m px py probeEnergy broadening := by
  unfold regularizedBastinTraceIntegrand projectorBastinTraceIntegrand
    projectorBastinOperatorIntegrand regularizedBastinOperatorIntegrand
    retardedAdvancedResolventDifference
  rw [retardedResolvent_eq_projectorResolvent v m px py probeEnergy broadening hE hbroadening]
  rw [advancedResolvent_eq_projectorResolvent v m px py probeEnergy broadening hE hbroadening]
  congr 1
  noncomm_ring

end

end AnomalousHall.MassiveDirac

import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Bridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.TraceKernel

set_option linter.style.header false

/-!
# Massive-Dirac Bastin projector blocks and Berry curvature

The finite-broadening Kubo–Bastin layer and the clean Berry-curvature layer share the same
massive-Dirac spectral projectors. This file makes that common block explicit without choosing an
eigenvector gauge.

The direction-indexed interband operator trace

```text
Tr(P_m j_μ P_n j_ν),  m = oppositeBand n,
```

is transported back to the concrete `2 × 2` matrix trace. Its antisymmetrization under
`μ ↔ ν` is the physical-current counterpart of the model-level force-matrix antisymmetrization,
and the `(x,y)` component reproduces `e² Ω_n` after division by the squared interband gap.

The projector-expanded finite-broadening Bastin kernel itself also remains direction-indexed.
Concrete Hall consumers specialize it to `(x,y)` downstream.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Gauge-independent direction-indexed interband current block in the bounded-operator
representation. -/
noncomputable def interbandCurrentTrace
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator (oppositeBand band) v m px py * currentOperator μ e v *
      bandProjectorOperator band v m px py * currentOperator ν e v)

/-- Replacing the bounded current vertices by the canonical electron-charge velocity
representatives leaves the interband current block unchanged. -/
theorem interbandCurrentTrace_eq_canonicalChargeVelocityTrace
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν band e v m px py =
      finiteDimensionalOperatorTrace
        (bandProjectorOperator (oppositeBand band) v m px py *
          ((((-e : ℝ) : ℂ)) • velocityOperator μ v) *
          bandProjectorOperator band v m px py *
          ((((-e : ℝ) : ℂ)) • velocityOperator ν v)) := by
  unfold interbandCurrentTrace
  rw [currentOperator_eq_charge_smul_velocityOperator,
    currentOperator_eq_charge_smul_velocityOperator]

/-- The bounded-operator interband current trace is exactly the ordinary matrix trace of the same
projector/current block. -/
theorem interbandCurrentTrace_eq_matrixTrace
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν band e v m px py =
      Matrix.trace
        (bandProjector (oppositeBand band) v m px py * current μ e v *
          bandProjector band v m px py * current ν e v) := by
  unfold interbandCurrentTrace
  simpa [bandProjectorOperator, currentOperator, matrixOperator] using
    finiteDimensionalOperatorTrace_toEuclideanCLM
      (bandProjector (oppositeBand band) v m px py * current μ e v *
        bandProjector band v m px py * current ν e v)

/-- Replacing direction-indexed charge currents by `-e` times the corresponding velocities pulls
out `e²` from the interband projector trace. -/
theorem matrixInterbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    Matrix.trace
        (bandProjector (oppositeBand band) v m px py * current μ e v *
          bandProjector band v m px py * current ν e v) =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
  simp [current, forceMatrixTraceNumerator]
  ring

/-- Operator form of the same direction-indexed `e²` factorization. -/
theorem interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν band e v m px py =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
  rw [interbandCurrentTrace_eq_matrixTrace]
  exact matrixInterbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    μ ν band e v m px py

/-- Exchanging the target band with its opposite is equivalent to reversing the ordered current
directions inside the interband trace. -/
theorem interbandCurrentTrace_oppositeBand_eq_swap
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν (oppositeBand band) e v m px py =
      interbandCurrentTrace ν μ band e v m px py := by
  unfold interbandCurrentTrace
  rw [oppositeBand_oppositeBand]
  calc
    finiteDimensionalOperatorTrace
        (bandProjectorOperator band v m px py * currentOperator μ e v *
          bandProjectorOperator (oppositeBand band) v m px py * currentOperator ν e v) =
      finiteDimensionalOperatorTrace
        ((bandProjectorOperator band v m px py * currentOperator μ e v) *
          (bandProjectorOperator (oppositeBand band) v m px py * currentOperator ν e v)) := by
      simp only [mul_assoc]
    _ = finiteDimensionalOperatorTrace
        ((bandProjectorOperator (oppositeBand band) v m px py * currentOperator ν e v) *
          (bandProjectorOperator band v m px py * currentOperator μ e v)) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator (oppositeBand band) v m px py * currentOperator ν e v *
          bandProjectorOperator band v m px py * currentOperator μ e v) := by
      simp only [mul_assoc]

/-- Antisymmetrization of the direction-indexed physical-current interband trace. -/
noncomputable def interbandCurrentTraceAntisymmetrization
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) : ℂ :=
  interbandCurrentTrace μ ν band e v m px py -
    interbandCurrentTrace ν μ band e v m px py

/-- Exchanging the current directions reverses the physical-current antisymmetrization. -/
theorem interbandCurrentTraceAntisymmetrization_swap
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTraceAntisymmetrization ν μ band e v m px py =
      -interbandCurrentTraceAntisymmetrization μ ν band e v m px py := by
  unfold interbandCurrentTraceAntisymmetrization
  ring

/-- The physical-current antisymmetrization vanishes on equal directions. -/
@[simp] theorem interbandCurrentTraceAntisymmetrization_self
    (μ : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTraceAntisymmetrization μ μ band e v m px py = 0 := by
  simp [interbandCurrentTraceAntisymmetrization]

/-- Exchanging the two bands reverses the current-trace antisymmetrization. -/
@[simp] theorem interbandCurrentTraceAntisymmetrization_oppositeBand
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTraceAntisymmetrization μ ν (oppositeBand band) e v m px py =
      -interbandCurrentTraceAntisymmetrization μ ν band e v m px py := by
  unfold interbandCurrentTraceAntisymmetrization
  rw [interbandCurrentTrace_oppositeBand_eq_swap μ ν,
    interbandCurrentTrace_oppositeBand_eq_swap ν μ]
  ring

/-- The physical-current antisymmetrization is `e²` times the force-matrix antisymmetrization. -/
theorem interbandCurrentTraceAntisymmetrization_eq_chargeSq_forceMatrixAntisymmetricNumerator
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTraceAntisymmetrization μ ν band e v m px py =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixAntisymmetricNumerator μ ν band v m px py := by
  unfold interbandCurrentTraceAntisymmetrization forceMatrixAntisymmetricNumerator
  rw [interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator μ ν,
    interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator ν μ]
  ring

/-- Berry-curvature weight formed from the antisymmetric physical-current interband trace. -/
noncomputable def interbandCurrentBerryWeight
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) : ℝ :=
  (interbandCurrentTraceAntisymmetrization μ ν band e v m px py).im /
    interbandEnergyGap band v m px py ^ 2

/-- The direction-indexed current-current Berry weight is `e²` times the corresponding force-matrix
Berry-curvature component. -/
theorem interbandCurrentBerryWeight_eq_chargeSq_forceMatrixBerryCurvatureComponent
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentBerryWeight μ ν band e v m px py =
      e ^ 2 * forceMatrixBerryCurvatureComponent μ ν band v m px py := by
  rw [interbandCurrentBerryWeight,
    interbandCurrentTraceAntisymmetrization_eq_chargeSq_forceMatrixAntisymmetricNumerator]
  unfold forceMatrixBerryCurvatureComponent
  push_cast
  simp [Complex.mul_im]
  ring

/-- The current-current Berry weight changes sign under exchange of the two bands. -/
@[simp] theorem interbandCurrentBerryWeight_oppositeBand
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentBerryWeight μ ν (oppositeBand band) e v m px py =
      -interbandCurrentBerryWeight μ ν band e v m px py := by
  unfold interbandCurrentBerryWeight
  rw [interbandCurrentTraceAntisymmetrization_oppositeBand, interbandEnergyGap_oppositeBand]
  simp

/-- Away from the Dirac degeneracy, the positively oriented physical-current component reproduces
`e²` times the clean two-dimensional Berry curvature. -/
theorem interbandCurrentBerryWeight_eq_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    interbandCurrentBerryWeight .x .y band e v m px py =
      e ^ 2 * berryCurvature band v m px py := by
  rw [interbandCurrentBerryWeight_eq_chargeSq_forceMatrixBerryCurvatureComponent]
  change e ^ 2 * forceMatrixBerryCurvature band v m px py =
    e ^ 2 * berryCurvature band v m px py
  rw [forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE]

/-- Bastin operator integrand with the generic Green operators replaced by their exact massive-Dirac
projector expansions for an ordered pair of current directions. -/
noncomputable def projectorBastinOperatorIntegrand
    (μ ν : Direction2) (e v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let retarded :=
    projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py
  let advanced :=
    projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py
  (currentOperator μ e v * retarded ^ 2 * currentOperator ν e v -
      currentOperator ν e v * advanced ^ 2 * currentOperator μ e v) *
    (retarded - advanced)

/-- Ordinary trace of the direction-indexed projector-expanded Bastin operator kernel. -/
noncomputable def projectorBastinTraceIntegrand
    (μ ν : Direction2) (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (projectorBastinOperatorIntegrand μ ν e v m px py probeEnergy broadening)

/-- Rewriting the current vertices as canonical electron-charge velocity representatives leaves the
direction-indexed Bastin trace integrand unchanged. -/
theorem regularizedBastinTraceIntegrand_eq_canonicalChargeVelocityVertices
    (μ ν : Direction2) (e v m px py probeEnergy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator μ e v) (currentOperator ν e v) probeEnergy broadening =
      regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        ((((-e : ℝ) : ℂ)) • velocityOperator μ v)
        ((((-e : ℝ) : ℂ)) • velocityOperator ν v) probeEnergy broadening := by
  rw [currentOperator_eq_charge_smul_velocityOperator,
    currentOperator_eq_charge_smul_velocityOperator]

/-- At nonzero broadening and away from the band degeneracy, the generic massive-Dirac Bastin trace
integrand is exactly the direction-indexed projector-expanded expression. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    (μ ν : Direction2) (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator μ e v) (currentOperator ν e v) probeEnergy broadening =
      projectorBastinTraceIntegrand μ ν e v m px py probeEnergy broadening := by
  unfold regularizedBastinTraceIntegrand projectorBastinTraceIntegrand
    projectorBastinOperatorIntegrand regularizedBastinOperatorIntegrand
    retardedAdvancedResolventDifference
  have hretarded :
      retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py := by
    simpa only [retardedResolvent, retardedSpectralParameter,
      spectralResolvent_retarded_ofRegulator, spectralParameter_retarded_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_projectorResolvent
        v m px py probeEnergy broadening hE hbroadening
  have hadvanced :
      advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py := by
    simpa only [advancedResolvent, advancedSpectralParameter,
      spectralResolvent_advanced_ofRegulator, spectralParameter_advanced_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_projectorResolvent
        v m px py probeEnergy (-broadening) hE
        (neg_ne_zero.mpr hbroadening)
  rw [hretarded, hadvanced]
  congr 1
  noncomm_ring

end

end QuantumTheory.Transport.Models.MassiveDirac

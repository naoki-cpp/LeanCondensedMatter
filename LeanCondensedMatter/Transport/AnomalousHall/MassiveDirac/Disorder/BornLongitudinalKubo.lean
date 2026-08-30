import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornPropagatorOperator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexNormalizationBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.CurrentBridge
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Born-dressed longitudinal retarded-advanced Kubo channel

This module inserts the massive-Dirac Born propagator into the generic finite-dimensional
retarded-advanced vertex trace block.  The measured vertex is the physical `x` charge current, while
the source vertex is supplied explicitly so a finite-broadening dressed current can be inserted
without first replacing it by its weak-disorder scalar limit.

A second bridge starts from the actual finite-cutoff operator integral already proved for
`Gᴿ_B σₓ Gᴬ_B`.  Multiplication by a left `σₓ` followed by the ordinary finite-dimensional trace
projects the full `σₓ`/`σᵧ` operator rung onto its longitudinal component: the `σᵧ` contribution is
retained through the operator identity and only vanishes when the trace pairing is evaluated.

No exact disorder average, weak-disorder limit, clean DC limit, SCBA/Ward statement, or RTA
conductivity theorem is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Pointwise finite-Born-width longitudinal RA trace channel with the physical `x` current as the
measured vertex and an arbitrary supplied source/dressed vertex. -/
noncomputable def continuumBornLongitudinalRetardedAdvancedTraceKernel
    (e v m px py probeEnergy disorderStrength hbar : ℝ)
    (dressedVertex : DiracHilbert →L[ℂ] DiracHilbert) : ℂ :=
  retardedAdvancedVertexTraceKernel
    (currentOperator .x e v)
    (continuumBornGreenOperator
      .retarded v m px py probeEnergy disorderStrength hbar)
    dressedVertex
    (continuumBornGreenOperator
      .advanced v m px py probeEnergy disorderStrength hbar)

/-- When the supplied dressed vertex is given by a concrete `2 × 2` matrix, the Born RA channel is
exactly the ordinary matrix trace of the corresponding four-factor block. -/
theorem continuumBornLongitudinalRetardedAdvancedTraceKernel_matrixVertex
    (e v m px py probeEnergy disorderStrength hbar : ℝ) (vertex : Matrix2) :
    continuumBornLongitudinalRetardedAdvancedTraceKernel
        e v m px py probeEnergy disorderStrength hbar (matrixOperator vertex) =
      Matrix.trace
        (current .x e v *
          continuumBornGreenMatrix
            .retarded v m px py probeEnergy disorderStrength hbar *
          vertex *
          continuumBornGreenMatrix
            .advanced v m px py probeEnergy disorderStrength hbar) := by
  unfold continuumBornLongitudinalRetardedAdvancedTraceKernel
    retardedAdvancedVertexTraceKernel twoGreenVertexTraceKernel
    continuumBornGreenOperator currentOperator
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change finiteDimensionalOperatorTrace
      (φ (current .x e v) *
        φ (continuumBornGreenMatrix
          .retarded v m px py probeEnergy disorderStrength hbar) *
        φ vertex *
        φ (continuumBornGreenMatrix
          .advanced v m px py probeEnergy disorderStrength hbar)) = _
  rw [← map_mul, ← map_mul, ← map_mul]
  exact finiteDimensionalOperatorTrace_matrixOperator _

private theorem finiteDimensionalOperatorTrace_sigmaX_mul_sigmaX :
    finiteDimensionalOperatorTrace
        (matrixOperator sigmaX * matrixOperator sigmaX) = (2 : ℂ) := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change finiteDimensionalOperatorTrace (φ sigmaX * φ sigmaX) = (2 : ℂ)
  rw [← map_mul]
  change finiteDimensionalOperatorTrace (matrixOperator (sigmaX * sigmaX)) = (2 : ℂ)
  rw [finiteDimensionalOperatorTrace_matrixOperator]
  norm_num [Matrix.trace, Matrix.mul_apply, sigmaX]

private theorem finiteDimensionalOperatorTrace_sigmaX_mul_sigmaY :
    finiteDimensionalOperatorTrace
        (matrixOperator sigmaX * matrixOperator sigmaY) = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change finiteDimensionalOperatorTrace (φ sigmaX * φ sigmaY) = 0
  rw [← map_mul]
  change finiteDimensionalOperatorTrace (matrixOperator (sigmaX * sigmaY)) = 0
  rw [finiteDimensionalOperatorTrace_matrixOperator]
  norm_num [Matrix.trace, Matrix.mul_apply, sigmaX, sigmaY]

/-- Finite-cutoff longitudinal RA Pauli trace obtained from the actual integrated Born operator
kernel, before attaching physical charge-current factors or the external disorder line. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXLongitudinalTrace
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (matrixOperator sigmaX *
      finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductIntegral
        v m probeEnergy disorderStrength hbar pMax)

/-- The actual finite-cutoff `Gᴿ_B σₓ Gᴬ_B` operator integral carries both `σₓ` and `σᵧ` channels,
but the longitudinal left-`σₓ` trace projects it exactly onto twice the integrated `σₓ`
Green-product coefficient.  The `σᵧ` channel is not discarded before this trace pairing. -/
theorem finiteCutoffContinuumBornRetardedAdvancedPauliXLongitudinalTrace_eq
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hX : IntervalIntegrable
      (fun p : ℝ =>
        continuumBornRetardedAdvancedPauliXRadialXIntegrand
            v m p probeEnergy disorderStrength hbar • matrixOperator sigmaX)
      volume 0 pMax)
    (hY : IntervalIntegrable
      (fun p : ℝ =>
        continuumBornRetardedAdvancedPauliXRadialYIntegrand
            v m p probeEnergy disorderStrength hbar • matrixOperator sigmaY)
      volume 0 pMax) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXLongitudinalTrace
        v m probeEnergy disorderStrength hbar pMax =
      2 * finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
        v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXLongitudinalTrace
  rw [finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductIntegral_eq_rung
    v m probeEnergy disorderStrength hbar pMax hX hY]
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXGreenProductRung
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  rw [map_add, map_smul, map_smul]
  rw [finiteDimensionalOperatorTrace_sigmaX_mul_sigmaX,
    finiteDimensionalOperatorTrace_sigmaX_mul_sigmaY]
  ring

/-- Exact finite-cutoff bridge between the longitudinal RA trace block and the normalized Born
current-rung coefficient.  The factor `1/2` is the Pauli trace pairing `Tr(σₓσₓ)=2`; the external
disorder-line / momentum-measure prefactor remains explicit. -/
theorem coe_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_prefactor_mul_half_longitudinalTrace
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hX : IntervalIntegrable
      (fun p : ℝ =>
        continuumBornRetardedAdvancedPauliXRadialXIntegrand
            v m p probeEnergy disorderStrength hbar • matrixOperator sigmaX)
      volume 0 pMax)
    (hY : IntervalIntegrable
      (fun p : ℝ =>
        continuumBornRetardedAdvancedPauliXRadialYIntegrand
            v m p probeEnergy disorderStrength hbar • matrixOperator sigmaY)
      volume 0 pMax) :
    (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient
        v m probeEnergy disorderStrength hbar pMax : ℂ) =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
        ((1 / 2 : ℂ) *
          finiteCutoffContinuumBornRetardedAdvancedPauliXLongitudinalTrace
            v m probeEnergy disorderStrength hbar pMax) := by
  rw [coe_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungXCoefficient_eq_prefactor_mul_greenProduct]
  rw [finiteCutoffContinuumBornRetardedAdvancedPauliXLongitudinalTrace_eq
    v m probeEnergy disorderStrength hbar pMax hX hY]
  ring

end

end AnomalousHall.MassiveDirac

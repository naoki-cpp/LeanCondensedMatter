import LeanCondensedMatter.Transport.Disorder.TraceBridge
import LeanCondensedMatter.Transport.Disorder.TwoParticleNormBound
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Quantitative finite-dimensional Středa two-Green trace control

The exact finite-ensemble mean of the pointwise two-Green current trace differs from the
trace formed from mean propagators by the **exact** connected insertion.

At two arbitrary nonzero signed regulators and a uniform potential bound `‖Vω‖ ≤ M`,
the difference is at most

```text
4 · dim(H) · ‖J_measured‖ · ‖J_source‖ · M² / (|γ_left|² |γ_right|²).
```

This is a fixed-regulator pointwise scalar trace estimate, NOT a bound against a supplied
Born/SCBA dressed-vertex approximation. In particular, it does not include same-side RR/AA,
Fermi-sea, contact, momentum integration, conductivity normalization, or a DC limit.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [FiniteDimensional ℂ H] [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The exact disorder-connected contribution to an averaged finite-dimensional two-Green
current trace is second order in a uniform impurity bound at fixed nonzero regulators.
The Hilbert-space dimension factor is explicit; no ladder approximation is assumed. -/
theorem norm_averagedTwoGreenTrace_sub_meanProduct_le_uniformPotential_sq
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregLeft : regulatorLeft ≠ 0) (hregRight : regulatorRight ≠ 0)
    (measuredVertex sourceVertex : H →L[ℂ] H)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight measuredVertex sourceVertex -
      twoGreenVertexTraceKernel measuredVertex
        (ensemble.averagedGreenOfRegulator energyLeft regulatorLeft)
        sourceVertex (ensemble.averagedGreenOfRegulator energyRight regulatorRight)‖ ≤
      ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) *
        ((2 * (|regulatorLeft|⁻¹) ^ 2 * potentialBound) * ‖sourceVertex‖ *
          (2 * (|regulatorRight|⁻¹) ^ 2 * potentialBound)) := by
  let conn := ensemble.connectedTwoGreenInsertionOfRegulators
    energyLeft regulatorLeft energyRight regulatorRight sourceVertex
  let trace := ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H)
  let limit := (2 * (|regulatorLeft|⁻¹) ^ 2 * potentialBound) * ‖sourceVertex‖ *
    (2 * (|regulatorRight|⁻¹) ^ 2 * potentialBound)
  have hconn : ‖conn‖ ≤ limit :=
    ensemble.norm_connectedTwoGreenInsertion_le_uniformPotential_sq
      energyLeft regulatorLeft energyRight regulatorRight hregLeft hregRight
      sourceVertex potentialBound hbound hpotential
  have hdiff :
      ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
          energyLeft regulatorLeft energyRight regulatorRight measuredVertex sourceVertex -
        twoGreenVertexTraceKernel measuredVertex
          (ensemble.averagedGreenOfRegulator energyLeft regulatorLeft)
          sourceVertex (ensemble.averagedGreenOfRegulator energyRight regulatorRight) =
      trace (measuredVertex * conn) := by
    rw [ensemble.averagedTwoGreenVertexTraceKernelOfRegulators_eq_mean_add_connected]
    abel
  rw [hdiff]
  change ‖trace (measuredVertex * conn)‖ ≤
    ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) * limit
  calc
    ‖trace (measuredVertex * conn)‖ ≤
        (Module.finrank ℂ H : ℝ) * ‖measuredVertex * conn‖ :=
      ContinuousLinearMap.norm_finiteDimensionalOperatorTrace_le_finrank_mul _
    _ ≤ (Module.finrank ℂ H : ℝ) * (‖measuredVertex‖ * ‖conn‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Nat.cast_nonneg _)
    _ ≤ (Module.finrank ℂ H : ℝ) * (‖measuredVertex‖ * limit) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hconn (norm_nonneg measuredVertex))
        (Nat.cast_nonneg _)
    _ = ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) * limit := by
      ring

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport

import LeanCondensedMatter.Transport.Disorder.TraceBridge
import LeanCondensedMatter.Transport.Disorder.TwoParticleNormBound
import LeanCondensedMatter.Analysis.Operator.FiniteTrace

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
    (potentialBound : ℝ)
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
      sourceVertex potentialBound hpotential
  rw [ensemble.averagedTwoGreenVertexTraceKernelOfRegulators_eq_mean_add_connected]
  simp only [add_sub_cancel_left]
  change ‖trace (measuredVertex * conn)‖ ≤
    ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) * limit
  exact (ContinuousLinearMap.norm_finiteDimensionalOperatorTrace_mul_le
    measuredVertex conn).trans
      (mul_le_mul_of_nonneg_left hconn
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport

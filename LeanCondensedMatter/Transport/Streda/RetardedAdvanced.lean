import LeanCondensedMatter.Transport.Streda.TraceKernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Retarded-advanced Fermi-surface trace channel

This module isolates the finite-dimensional two-Green trace block

```text
Tr[J_meas G_left Γ G_right]
```

that carries the retarded-advanced (RA) part of the Středa Fermi-surface response.  The supplied
Green operators and source vertex are kept independent, so downstream disorder approximations can
reuse this algebra without being identified with the exact clean resolvent.

For arbitrary measured/source vertices, the clean regularized Smrčka–Středa surface primitive trace
is exactly the RA block minus an explicit same-side RR/AA half-sum.  No same-side term is dropped,
and no disorder, zero-broadening, DC, or thermodynamic-limit claim is made here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Finite-dimensional trace block with independently supplied left/right Green operators and
measured/source vertices.  This neutral owner is reused by the RA and same-side specializations. -/
noncomputable def twoGreenVertexTraceKernel
    (measuredVertex leftGreen sourceVertex rightGreen : H →L[ℂ] H) : ℂ :=
  finiteDimensionalOperatorTrace
    (measuredVertex * leftGreen * sourceVertex * rightGreen)

/-- Retarded-advanced vertex trace block `Tr[J_meas Gᴿ Γ Gᴬ]` for supplied Green operators. -/
noncomputable def retardedAdvancedVertexTraceKernel
    (measuredVertex retardedGreen sourceVertex advancedGreen : H →L[ℂ] H) : ℂ :=
  twoGreenVertexTraceKernel measuredVertex retardedGreen sourceVertex advancedGreen

/-- Explicit same-side half-sum accompanying the RA block for arbitrary measured/source vertices.
The advanced term retains the current order produced directly by the Smrčka–Středa surface factor. -/
noncomputable def sameSideVertexTraceRemainder
    (measuredVertex sourceVertex retardedGreen advancedGreen : H →L[ℂ] H) : ℂ :=
  (1 / 2 : ℂ) *
    (twoGreenVertexTraceKernel measuredVertex retardedGreen sourceVertex retardedGreen +
      twoGreenVertexTraceKernel sourceVertex advancedGreen measuredVertex advancedGreen)

/-- Supplied-Green Středa surface trace kernel.  This is only the finite-dimensional trace algebra
`RA - same-side`; downstream approximations decide which Green operators and source vertex to
supply. -/
noncomputable def suppliedGreenStredaSurfacePrimitiveTraceKernel
    (measuredVertex retardedGreen sourceVertex advancedGreen : H →L[ℂ] H) : ℂ :=
  retardedAdvancedVertexTraceKernel
      measuredVertex retardedGreen sourceVertex advancedGreen -
    sameSideVertexTraceRemainder
      measuredVertex sourceVertex retardedGreen advancedGreen

/-- For arbitrary current vertices, the clean regularized Středa surface primitive is exactly the
supplied-Green `RA - RR/AA` trace kernel evaluated on the canonical resolvents. -/
theorem regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
    (hamiltonian measuredVertex sourceVertex : H →L[ℂ] H)
    (energy broadening : ℝ) :
    regularizedStredaSurfacePrimitiveTrace
        hamiltonian measuredVertex sourceVertex energy broadening =
      suppliedGreenStredaSurfacePrimitiveTraceKernel
        measuredVertex
        (retardedResolvent hamiltonian energy broadening)
        sourceVertex
        (advancedResolvent hamiltonian energy broadening) := by
  let R : H →L[ℂ] H := retardedResolvent hamiltonian energy broadening
  let A : H →L[ℂ] H := advancedResolvent hamiltonian energy broadening
  have hcyclic :
      finiteDimensionalOperatorTrace (sourceVertex * A * measuredVertex * R) =
        finiteDimensionalOperatorTrace (measuredVertex * R * sourceVertex * A) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (sourceVertex * A) (measuredVertex * R))
  have hexpand :
      (measuredVertex * R * sourceVertex - sourceVertex * A * measuredVertex) * (R - A) =
        measuredVertex * R * sourceVertex * R - measuredVertex * R * sourceVertex * A -
          sourceVertex * A * measuredVertex * R + sourceVertex * A * measuredVertex * A := by
    noncomm_ring
  unfold regularizedStredaSurfacePrimitiveTrace
    regularizedStredaSurfacePrimitiveOperator smrckaStredaSurfaceFactor
    retardedAdvancedResolventDifference suppliedGreenStredaSurfacePrimitiveTraceKernel
    retardedAdvancedVertexTraceKernel sameSideVertexTraceRemainder twoGreenVertexTraceKernel
  change finiteDimensionalOperatorTrace
      ((-(1 / 2 : ℂ)) •
        ((measuredVertex * R * sourceVertex - sourceVertex * A * measuredVertex) * (R - A))) = _
  rw [hexpand]
  simp only [map_smul, map_add, map_sub]
  rw [hcyclic]
  ring

end
end Transport
end QuantumTheory

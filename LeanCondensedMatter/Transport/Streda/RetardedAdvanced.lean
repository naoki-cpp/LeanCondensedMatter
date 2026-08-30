import LeanCondensedMatter.Transport.Streda.TraceKernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Retarded-advanced Fermi-surface trace channel

This module isolates the finite-dimensional two-Green trace block

```text
Tr[J_meas G_left Γ G_right]
```

that carries the retarded-advanced (RA) part of the longitudinal Fermi-surface response.  The
supplied Green operators and source vertex are kept independent, so downstream disorder
approximations can reuse this algebra without being identified with the exact clean resolvent.

For the clean longitudinal specialization, the existing regularized Smrčka–Středa surface
primitive trace is proved to be the RA block minus the explicit half-sum of the same-side RR and AA
blocks.  This is an exact finite-broadening trace identity.  It does not discard the same-side
remainder and makes no disorder, zero-broadening, DC, or thermodynamic-limit claim.
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

/-- Explicit same-side half-sum accompanying the RA block in the longitudinal Středa surface
primitive. -/
noncomputable def longitudinalSameSideTraceRemainder
    (current retardedGreen advancedGreen : H →L[ℂ] H) : ℂ :=
  (1 / 2 : ℂ) *
    (twoGreenVertexTraceKernel current retardedGreen current retardedGreen +
      twoGreenVertexTraceKernel current advancedGreen current advancedGreen)

/-- For identical longitudinal current vertices, the clean regularized Středa surface primitive is
exactly the RA trace block minus the explicit RR/AA half-sum.  No same-side term is dropped. -/
theorem regularizedStredaSurfacePrimitiveTrace_longitudinal_eq_ra_sub_sameSide
    (hamiltonian current : H →L[ℂ] H) (energy broadening : ℝ) :
    regularizedStredaSurfacePrimitiveTrace
        hamiltonian current current energy broadening =
      retardedAdvancedVertexTraceKernel
          current
          (retardedResolvent hamiltonian energy broadening)
          current
          (advancedResolvent hamiltonian energy broadening) -
        longitudinalSameSideTraceRemainder
          current
          (retardedResolvent hamiltonian energy broadening)
          (advancedResolvent hamiltonian energy broadening) := by
  let R : H →L[ℂ] H := retardedResolvent hamiltonian energy broadening
  let A : H →L[ℂ] H := advancedResolvent hamiltonian energy broadening
  have hcyclic :
      finiteDimensionalOperatorTrace (current * A * current * R) =
        finiteDimensionalOperatorTrace (current * R * current * A) := by
    simpa [mul_assoc] using
      (finiteDimensionalOperatorTrace_mul_comm
        (H := H) (current * A) (current * R))
  have hexpand :
      (current * R * current - current * A * current) * (R - A) =
        current * R * current * R - current * R * current * A -
          current * A * current * R + current * A * current * A := by
    noncomm_ring
  unfold regularizedStredaSurfacePrimitiveTrace
    regularizedStredaSurfacePrimitiveOperator smrckaStredaSurfaceFactor
    retardedAdvancedResolventDifference retardedAdvancedVertexTraceKernel
    longitudinalSameSideTraceRemainder twoGreenVertexTraceKernel
  change finiteDimensionalOperatorTrace
      ((-(1 / 2 : ℂ)) • ((current * R * current - current * A * current) * (R - A))) = _
  rw [hexpand]
  simp only [map_smul, map_add, map_sub]
  rw [hcyclic]
  ring

end
end Transport
end QuantumTheory

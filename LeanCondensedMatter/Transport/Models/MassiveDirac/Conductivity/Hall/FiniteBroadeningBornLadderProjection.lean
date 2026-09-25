import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderWeakDisorder

set_option linter.style.header false

/-!
# Hall projection of the massive-Dirac Born-Dyson conductivity tensor

The finite-`η` massive-Dirac Středa conductivity is represented directly as a
`ConductivityTensor (Fin 2)`. The neutral Conductivity module owns its rotational closure and
zero-broadening tensor boundary. This module consumes that seam to expose the antisymmetric Hall
projection.

The Hall component is the antisymmetric tensor projection rather than a label attached to an
ordered response. Its subsequent one-sided weak-disorder limit is inherited from the ordered `xy`
endpoint. Identification with external closed-form benchmarks belongs to downstream benchmark
modules.

The cutoff remains fixed beyond the metallic shell, and the limits remain sequential: `η → 0⁺` at
fixed positive disorder, then `W → 0⁺`. No ultraviolet/thermodynamic/simultaneous limit, crossed
`X/Ψ` contribution, mechanism decomposition, or exact disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- The antisymmetric Hall projection of the zero-broadening tensor equals its ordered `xy`
component exactly. -/
@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_xy
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax).hallComponent 0 1 =
      finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax := by
  simp [ConductivityTensor.hallComponent,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary]

/-- The fixed-cutoff Hall projection has the same one-sided weak-disorder limit as the ordered `xy`
endpoint, now interpreted as the antisymmetric part of a completed conductivity tensor. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax).hallComponent 0 1)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ))) := by
  simpa only [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_xy] using
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff

end

end QuantumTheory.Transport.Models.MassiveDirac

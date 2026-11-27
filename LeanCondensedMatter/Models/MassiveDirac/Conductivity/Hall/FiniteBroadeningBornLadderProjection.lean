import LeanCondensedMatter.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.HallZeroBroadeningWeakDisorder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Hall projection of the massive-Dirac Born-Dyson conductivity tensor

The finite-`η` massive-Dirac Středa conductivity is represented directly as a
`ConductivityTensor (Fin 2)`. The neutral Conductivity module owns its rotational closure and
zero-broadening tensor boundary. This module consumes that seam to expose the antisymmetric Hall
projection.

The Hall component is the antisymmetric tensor projection rather than a label attached to an
ordered response. Its one-sided weak-disorder limit uses the upstream ordered `xy` momentum-integral
limit with physical Bastin/Středa normalization. The ordered response is only a local proof step;
the tensor projection is the public endpoint. Identification with external closed-form benchmarks
belongs to downstream benchmark modules.

The cutoff remains fixed beyond the metallic shell, and the limits remain sequential: `η → 0⁺` at
fixed positive disorder, then `W → 0⁺`. No ultraviolet/thermodynamic/simultaneous limit, crossed
`X/Ψ` contribution, mechanism decomposition, or exact disorder-average claim is introduced here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open Filter QuantumTheory.Transport

namespace FiniteCutoffBornDyson.Hall.ZeroBroadeningWeakDisorder

/-- The fixed-cutoff Hall projection has the same one-sided weak-disorder limit as the ordered `xy`
endpoint and is the antisymmetric projection of the conductivity tensor. -/
theorem tendsto_hallComponent
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
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  have hresponse :=
    tendsto_orderedXY_momentumIntegral
      e v m probeEnergy hbar pMax hvelocity hhbarNe hmetal hcutoff
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      (((bastinStredaPhysicalMomentumConductivityNormalization hbar : ℝ) : ℂ)) *
          (((-16 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
            (probeEnergy ^ 2 + m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ)) =
        (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) := by
    unfold bastinStredaPhysicalMomentumConductivityNormalization bastinStredaConductivityNormalization
      bastinStredaTraceConductivityPrefactor
      momentumMeasurePrefactor
    push_cast
    field_simp [hhbarNe, hden, Real.pi_ne_zero]
    ring
  have hnormalized :=
    hresponse.const_mul (((bastinStredaPhysicalMomentumConductivityNormalization hbar : ℝ) : ℂ))
  rw [htarget] at hnormalized
  simpa [ConductivityTensor.hallComponent,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary,
    finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary] using hnormalized

end FiniteCutoffBornDyson.Hall.ZeroBroadeningWeakDisorder

end

end QuantumTheory.Models.MassiveDirac

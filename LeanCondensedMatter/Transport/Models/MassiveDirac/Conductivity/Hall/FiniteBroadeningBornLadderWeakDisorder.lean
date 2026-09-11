import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening ordered transverse conductivity

This module attaches the canonical Bastin/Středa and physical-momentum normalization to the upstream
fixed-cutoff ordered source-`.y` weak-disorder response. The limit is sequential: `η → 0⁺` is taken
first at fixed positive disorder and only then `W → 0⁺`.

The resulting ordered `xy` coefficient has the non-crossing massive-Dirac regression form in `ℏ`
normalization, but it is not yet identified with the antisymmetric Hall projection. No ultraviolet,
thermodynamic, crossed-diagram, mechanism-decomposition, or simultaneous-limit claim is introduced.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- The physically normalized fixed-cutoff zero-broadening ordered source-`.y` conductivity has a
finite one-sided weak-disorder limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ))) := by
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  have hresponse :=
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbarNe hmetal hcutoff
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      (((bastinStredaConductivityNormalization hbar : ℝ) : ℂ)) *
          (((-16 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
            (probeEnergy ^ 2 + m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ)) =
        (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
          (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) := by
    unfold bastinStredaConductivityNormalization bastinTraceConductivityPrefactor
      momentumMeasurePrefactor
    push_cast
    field_simp [hhbarNe, hden, Real.pi_ne_zero]
    ring
  have hnormalized :=
    hresponse.const_mul (((bastinStredaConductivityNormalization hbar : ℝ) : ℂ))
  rw [htarget] at hnormalized
  simpa [
    finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary] using
    hnormalized

end

end QuantumTheory.Transport.Models.MassiveDirac

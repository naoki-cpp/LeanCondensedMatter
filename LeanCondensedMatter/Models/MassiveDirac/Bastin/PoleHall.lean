import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Hall-direction target-centered massive-Dirac Bastin pole factor

The direction-indexed interband spectator is defined upstream by `PoleFactor`. This module
specializes it to the ordered Hall current pair `(x,y)` in target-centered energy coordinates,
identifies it with the generic interband-pole regular factor, and evaluates its target-pole value.

Regularity of the generic factor away from the shifted interband gap is already available through
`Transport.Streda.InterbandPole` without a model-specific continuity wrapper.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The regular Hall interband spectator/current factor written in target-centered coordinates
`(offset, broadening)`. -/
noncomputable def targetCenteredInterbandSpectatorCurrentFactor
    (band : Band) (e v m px py : ℝ) (offsetBroadening : ℝ × ℝ) : ℂ :=
  interbandSpectatorCurrentFactor 0 1 band e v m px py
    (bandEnergy band v m px py + offsetBroadening.1) offsetBroadening.2

/-- The model-specific target-centered spectator is exactly the generic isolated interband-pole
regular factor with the massive-Dirac gap and ordered Hall current blocks supplied. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor
    (band : Band) (e v m px py : ℝ) (p : ℝ × ℝ) :
    targetCenteredInterbandSpectatorCurrentFactor band e v m px py p =
      interbandPoleRegularFactor
        (interbandEnergyGap band v m px py)
        (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
        (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
        p := by
  unfold targetCenteredInterbandSpectatorCurrentFactor
    interbandSpectatorCurrentFactor interbandPoleRegularFactor
  dsimp
  simp only [retardedSpectralParameter, advancedSpectralParameter]
  rw [projectorResolventCoefficient_targetOffset_oppositeBand
      .retarded band v m px py p.1 p.2,
    projectorResolventCoefficient_targetOffset_oppositeBand
      .advanced band v m px py p.1 p.2,
    targetCenteredSourceCoefficient_eq
      .retarded (interbandEnergyGap band v m px py) p.1 p.2,
    targetCenteredSourceCoefficient_eq
      .advanced (interbandEnergyGap band v m px py) p.1 p.2]

/-- At zero offset and zero broadening, the regular factor is exactly the inverse-gap-squared
canonical antisymmetric Hall current block. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) :
    targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0) =
      (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
        bastinInterbandBlockDifference 0 1 band e v m px py) := by
  rw [targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor,
    interbandPoleRegularFactor_zero]
  simp [bastinInterbandBlockDifference]

end

end QuantumTheory.Models.MassiveDirac

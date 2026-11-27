import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleFactor
import LeanCondensedMatter.QuantumTheory.TwoBand
import LeanCondensedMatter.Transport.Streda.InterbandPole

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

open QuantumTheory.Transport QuantumTheory.TwoBand

/-- The regular Hall interband spectator/current factor written in target-centered coordinates
`(offset, broadening)`. -/
noncomputable def targetCenteredInterbandSpectatorCurrentFactor
    (band : TwoBand) (e v m px py : ℝ) (offsetBroadening : ℝ × ℝ) : ℂ :=
  interbandSpectatorCurrentFactor 0 1 band e v m px py
    (bandEnergy band v m px py + offsetBroadening.1) offsetBroadening.2

/-- The model-specific target-centered spectator is exactly the generic isolated interband-pole
regular factor with the massive-Dirac gap and ordered Hall current blocks supplied. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor
    (band : TwoBand) (e v m px py : ℝ) (p : ℝ × ℝ) :
    targetCenteredInterbandSpectatorCurrentFactor band e v m px py p =
      interbandPoleRegularFactor
        (interbandEnergyGap band v m px py)
        (currentBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
        (currentBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
        p := by
  unfold targetCenteredInterbandSpectatorCurrentFactor
    interbandSpectatorCurrentFactor interbandPoleRegularFactor
  dsimp
  simp only [retardedSpectralParameter, advancedSpectralParameter,
    scalarResolventCoefficient_targetCentered, interbandEnergyGap]

end

end QuantumTheory.Models.MassiveDirac

import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuity of the massive-Dirac Bastin spectator

The target-band Lorentzian kernel depends on the energy offset from the pole and on the spectral
broadening. The opposite-band spectator/current factor is regular wherever the shifted interband
gap stays nonzero.

This file rewrites the opposite-band resolvent in target-centered coordinates, specializes the
generic spectator factor to the Hall direction pair `(x,y)`, evaluates it at the pole, and proves
joint continuity away from the shifted gap zero. Fixed-window integration lives downstream.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open Filter QuantumTheory.Transport

/-- In target-centered offset coordinates, the opposite-band spectator denominator on spectral side
`s` is `gap + offset + i γˢ`. -/
private theorem projectorResolventCoefficient_targetOffset_oppositeBand
    (side : SpectralSide) (band : Band) (v m px py offset broadening : ℝ) :
    projectorResolventCoefficient
        (spectralParameter side
          (bandEnergy band v m px py + offset) broadening)
        (oppositeBand band) v m px py =
      ((((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) +
          ((side.regulator broadening : ℝ) : ℂ) * Complex.I))⁻¹ := by
  unfold projectorResolventCoefficient spectralParameter spectralParameterOfRegulator
    interbandEnergyGap
  congr 1
  push_cast
  ring

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

/-- If the real shifted interband gap is nonzero at an offset, then the target-centered regular
spectator/current factor is jointly continuous there for arbitrary real broadening. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
    (band : Band) (e v m px py : ℝ) (p : ℝ × ℝ)
    (hshift : interbandEnergyGap band v m px py + p.1 ≠ 0) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      p := by
  have hfun :
      targetCenteredInterbandSpectatorCurrentFactor band e v m px py =
        interbandPoleRegularFactor
          (interbandEnergyGap band v m px py)
          (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
          (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py) := by
    funext q
    exact targetCenteredInterbandSpectatorCurrentFactor_eq_interbandPoleRegularFactor
      band e v m px py q
  rw [hfun]
  exact continuousAt_interbandPoleRegularFactor_of_gap_add_offset_ne_zero
    (interbandEnergyGap band v m px py)
    (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
    (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
    p hshift

end

end QuantumTheory.Models.MassiveDirac

import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Target-centered interband Bastin pole window

The occupation-weighted pole limit will integrate over a fixed energy window centered at a selected
massive-Dirac band energy.  The Lorentzian factor is singular at that target pole, but the
opposite-band spectator resolvent must remain uniformly separated from its own source-band pole.

This file rewrites the opposite-band spectral-side denominator in target-centered offset coordinates
and records the elementary real-gap separation needed for later uniform estimates. No integral or
limit/interchange theorem is proved here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- In target-centered offset coordinates, the opposite-band spectator denominator on spectral side
`s` is `gap + offset + i γˢ`. -/
theorem projectorResolventCoefficient_targetOffset_oppositeBand
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

end

end QuantumTheory.Models.MassiveDirac

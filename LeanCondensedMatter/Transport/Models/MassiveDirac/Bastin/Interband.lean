import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Spectator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Symmetry
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Interband Bastin block antisymmetry for the massive Dirac model

At a target-band Bastin pole, the source band is the opposite band. The two current orderings are
coordinates of one direction-indexed interband block, so this module keeps them generic in
`Direction2` and exposes their antisymmetric difference as the canonical object.

Cyclicity identifies that Bastin block difference with minus the antisymmetrization of the physical
interband current trace. After division by the squared interband gap, the `(x,y)` component is
therefore minus `e²` times the clean two-dimensional Berry curvature away from the Dirac
degeneracy.

No energy integration, zero-broadening limit/integral interchange, or momentum integration is
performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- With the source chosen as the opposite band, a direction-indexed Bastin block is the interband
current trace whose target label is the opposite band. -/
theorem bastinBandBlockTrace_opposite_source
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    bastinBandBlockTrace μ ν (oppositeBand band) band e v m px py =
      interbandCurrentTrace μ ν (oppositeBand band) e v m px py := by
  rw [bastinBandBlockTrace_eq_currentBandBlockTrace]
  cases band <;> rfl

/-- Reversing the current ordering of an opposite-source Bastin block gives the interband current
trace of the selected target band. -/
theorem bastinBandBlockTrace_swap_opposite_source
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    bastinBandBlockTrace ν μ (oppositeBand band) band e v m px py =
      interbandCurrentTrace μ ν band e v m px py := by
  rw [bastinBandBlockTrace_swap_eq_currentBandBlockTrace]
  cases band <;> rfl

/-- Antisymmetric direction exchange of the interband Bastin block at a selected target band. -/
noncomputable def bastinInterbandBlockDifference
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) : ℂ :=
  bastinBandBlockTrace μ ν (oppositeBand band) band e v m px py -
    bastinBandBlockTrace ν μ (oppositeBand band) band e v m px py

/-- Exchanging the two current directions reverses the sign of the interband Bastin block
difference. -/
theorem bastinInterbandBlockDifference_swap
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    bastinInterbandBlockDifference ν μ band e v m px py =
      -bastinInterbandBlockDifference μ ν band e v m px py := by
  unfold bastinInterbandBlockDifference
  ring

/-- The antisymmetric interband Bastin block vanishes on equal current directions. -/
theorem bastinInterbandBlockDifference_self
    (μ : Direction2) (band : Band) (e v m px py : ℝ) :
    bastinInterbandBlockDifference μ μ band e v m px py = 0 := by
  simp [bastinInterbandBlockDifference]

/-- The canonical antisymmetric Bastin block is the difference of the two opposite interband
current traces for the same ordered direction pair. -/
theorem bastinInterbandBlockDifference_eq_currentTraceDifference
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    bastinInterbandBlockDifference μ ν band e v m px py =
      interbandCurrentTrace μ ν (oppositeBand band) e v m px py -
        interbandCurrentTrace μ ν band e v m px py := by
  unfold bastinInterbandBlockDifference
  rw [bastinBandBlockTrace_opposite_source,
    bastinBandBlockTrace_swap_opposite_source]

/-- Cyclicity turns the opposite-source Bastin block difference into minus the current-trace
antisymmetrization for the selected target band. -/
theorem bastinInterbandBlockDifference_eq_neg_currentTraceAntisymmetrization
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    bastinInterbandBlockDifference μ ν band e v m px py =
      -interbandCurrentTraceAntisymmetrization μ ν band e v m px py := by
  rw [bastinInterbandBlockDifference_eq_currentTraceDifference,
    interbandCurrentTrace_oppositeBand_eq_swap]
  unfold interbandCurrentTraceAntisymmetrization
  ring

/-- At a target-band pole, the normalized imaginary antisymmetric Bastin current block is minus the
corresponding direction-indexed physical-current Berry weight. -/
theorem bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_berryWeight
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    (bastinInterbandBlockDifference μ ν band e v m px py).im /
        interbandEnergyGap band v m px py ^ 2 =
      -interbandCurrentBerryWeight μ ν band e v m px py := by
  rw [bastinInterbandBlockDifference_eq_neg_currentTraceAntisymmetrization]
  unfold interbandCurrentBerryWeight
  simp

/-- Consequently the normalized positively oriented Bastin block is the negative of `e²` times the
clean two-dimensional Berry curvature. -/
theorem bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (bastinInterbandBlockDifference .x .y band e v m px py).im /
        interbandEnergyGap band v m px py ^ 2 =
      -(e ^ 2 * berryCurvature band v m px py) := by
  rw [bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_berryWeight .x .y,
    interbandCurrentBerryWeight_eq_chargeSq_berryCurvature band e v m px py hE]

end

end QuantumTheory.Transport.Models.MassiveDirac

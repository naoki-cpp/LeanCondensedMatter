import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Spectator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Symmetry
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Interband Bastin block antisymmetry for the massive Dirac model

At a target-band Bastin pole, the source band is the opposite band. The natural `x-y` and `y-x`
trace orderings therefore reduce to the two opposite interband current traces already used by the
clean Berry-curvature bridge.

This file records the band-exchange symmetry needed by the next occupation-weighted pole limit.
The imaginary part of the `x-y` minus `y-x` block, normalized by the squared interband energy gap,
is exactly minus the physical-current Berry weight and hence minus `e²` times the clean Berry
curvature away from the Dirac degeneracy.

No energy integration, zero-broadening limit/integral interchange, or momentum integration is
performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- With the source chosen as the opposite band, the natural Bastin `x-y` trace is the Hall
interband current trace whose target label is the opposite band. -/
theorem bastinXYBandBlockTrace_opposite_source
    (band : Band) (e v m px py : ℝ) :
    bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py =
      interbandCurrentTrace .x .y (oppositeBand band) e v m px py := by
  rw [bastinBandBlockTrace_eq_currentBandBlockTrace]
  cases band <;> rfl

/-- The corresponding `y-x` Bastin trace is the Hall interband current trace of the selected target
band. -/
theorem bastinYXBandBlockTrace_opposite_source
    (band : Band) (e v m px py : ℝ) :
    bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py =
      interbandCurrentTrace .x .y band e v m px py := by
  rw [bastinBandBlockTrace_swap_eq_currentBandBlockTrace]
  cases band <;> rfl

/-- The imaginary parts of the two Hall interband current traces are opposite away from the band
degeneracy. -/
theorem interbandCurrentTrace_oppositeBand_im
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (interbandCurrentTrace .x .y (oppositeBand band) e v m px py).im =
      -(interbandCurrentTrace .x .y band e v m px py).im := by
  rw [interbandCurrentTrace_im (oppositeBand band) e v m px py,
    interbandCurrentTrace_im band e v m px py,
    forceMatrixTraceNumerator_im (oppositeBand band) v m px py hE,
    forceMatrixTraceNumerator_im band v m px py hE]
  cases band <;> simp [oppositeBand, bandSign] <;> ring

/-- The physical-current Berry weight changes sign under exchange of the two bands. -/
theorem interbandCurrentBerryWeight_oppositeBand
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    interbandCurrentBerryWeight (oppositeBand band) e v m px py =
      -interbandCurrentBerryWeight band e v m px py := by
  rw [interbandCurrentBerryWeight_eq_chargeSq_berryCurvature
      (oppositeBand band) e v m px py hE,
    interbandCurrentBerryWeight_eq_chargeSq_berryCurvature band e v m px py hE,
    berryCurvature_oppositeBand]
  ring

/-- At a target-band pole, the normalized imaginary antisymmetric Bastin current block is minus the
Berry weight of that target band. -/
theorem bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_berryWeight
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ((bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
        bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py).im /
      interbandEnergyGap band v m px py ^ 2) =
      -interbandCurrentBerryWeight band e v m px py := by
  rw [bastinXYBandBlockTrace_opposite_source,
    bastinYXBandBlockTrace_opposite_source,
    Complex.sub_im,
    interbandCurrentTrace_oppositeBand_im band e v m px py hE]
  unfold interbandCurrentBerryWeight
  ring

/-- Consequently the normalized antisymmetric Bastin block is the negative of `e²` times the clean
Berry curvature. -/
theorem bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ((bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
        bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py).im /
      interbandEnergyGap band v m px py ^ 2) =
      -(e ^ 2 * berryCurvature band v m px py) := by
  rw [bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_berryWeight
      band e v m px py hE,
    interbandCurrentBerryWeight_eq_chargeSq_berryCurvature band e v m px py hE]

end

end QuantumTheory.Transport.Models.MassiveDirac

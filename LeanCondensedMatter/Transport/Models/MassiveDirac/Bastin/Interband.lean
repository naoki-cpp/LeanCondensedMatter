import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Spectator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Symmetry
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Interband Bastin block antisymmetry for the massive Dirac model

At a target-band Bastin pole, the source band is the opposite band. The two current orderings are
coordinates of one direction-indexed interband block, so this module keeps them generic in
`Direction2` and exposes their antisymmetric difference as the canonical Bastin object. The ordered
projector-first current blocks themselves are model-level spectral data owned by
`Model/OperatorSpectral`.

The imaginary part of the Hall antisymmetric block, normalized by the squared interband energy gap,
is exactly minus `e²` times the clean Berry curvature away from the Dirac degeneracy.

No energy integration, zero-broadening limit/integral interchange, or momentum integration is
performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

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

/-- The normalized Hall antisymmetric Bastin block is the negative of `e²` times the clean Berry
curvature. -/
theorem bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (bastinInterbandBlockDifference .x .y band e v m px py).im /
        interbandEnergyGap band v m px py ^ 2 =
      -(e ^ 2 * berryCurvature band v m px py) := by
  have hband :=
    two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
      band e v m px py hE
  have hopp :=
    two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
      (oppositeBand band) e v m px py hE
  rw [interbandEnergyGap_oppositeBand, berryCurvature_oppositeBand] at hopp
  simp [pow_two] at hopp
  unfold bastinInterbandBlockDifference
  rw [bastinBandBlockTrace_swap .x .y (oppositeBand band) band]
  rw [bastinBandBlockTrace_eq_currentBandBlockTrace .x .y (oppositeBand band) band,
    bastinBandBlockTrace_eq_currentBandBlockTrace .x .y band (oppositeBand band),
    Complex.sub_im]
  have hgap := interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  field_simp [hgap] at hband hopp ⊢
  nlinarith

end

end QuantumTheory.Transport.Models.MassiveDirac

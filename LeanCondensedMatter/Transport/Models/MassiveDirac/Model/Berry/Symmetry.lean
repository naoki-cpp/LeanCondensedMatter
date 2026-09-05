import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Bridge

set_option linter.style.header false

/-!
# Symmetry checks for the clean massive-Dirac Berry curvature

The closed massive-Dirac Berry curvature must

- be odd under reversal of the time-reversal-breaking mass `m`;
- vanish in the massless model;
- have opposite signs in the two bands.

The algebraic `berryCurvature` definition is total even when `E = 0`, because Lean's field
division is total. The algebraic massless identity therefore needs no nondegeneracy hypothesis,
while force-matrix/projector statements retain it where the spectral projectors require `E ≠ 0`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Reversing the Dirac mass leaves the positive dispersion unchanged. -/
theorem energy_neg_mass (v m px py : ℝ) :
    energy v (-m) px py = energy v m px py := by
  unfold energy energySq
  congr 1
  ring

/-- The upper- and lower-band Berry curvatures are opposite. -/
theorem berryCurvature_oppositeBand (band : Band) (v m px py : ℝ) :
    berryCurvature (oppositeBand band) v m px py =
      -berryCurvature band v m px py := by
  cases band <;>
    simp [oppositeBand, berryCurvature_upper, berryCurvature_lower] <;>
    ring

/-- Reversing the time-reversal-breaking mass reverses the Berry curvature. -/
theorem berryCurvature_neg_mass (band : Band) (v m px py : ℝ) :
    berryCurvature band v (-m) px py =
      -berryCurvature band v m px py := by
  have hE : energy v (-m) px py = energy v m px py := energy_neg_mass v m px py
  cases band <;>
    simp [berryCurvature_upper, berryCurvature_lower, hE] <;>
    ring

/-- Removing the mass gives zero algebraic Berry curvature. -/
theorem berryCurvature_massless (band : Band) (v px py : ℝ) :
    berryCurvature band v 0 px py = 0 := by
  cases band <;>
    simp [berryCurvature_upper, berryCurvature_lower]

/-- The force-matrix/projector curvature inherits the odd-in-mass symmetry away from the band
degeneracy. -/
theorem forceMatrixBerryCurvature_neg_mass (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixBerryCurvature band v (-m) px py =
      -forceMatrixBerryCurvature band v m px py := by
  have hEneg : energy v (-m) px py ≠ 0 := by
    simpa [energy_neg_mass] using hE
  rw [forceMatrixBerryCurvature_eq_berryCurvature band v (-m) px py hEneg]
  rw [forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE]
  exact berryCurvature_neg_mass band v m px py

/-- The force-matrix/projector curvature vanishes in the massless nondegenerate model. -/
theorem forceMatrixBerryCurvature_massless (band : Band) (v px py : ℝ)
    (hE : energy v 0 px py ≠ 0) :
    forceMatrixBerryCurvature band v 0 px py = 0 := by
  rw [forceMatrixBerryCurvature_eq_berryCurvature band v 0 px py hE]
  exact berryCurvature_massless band v px py

end

end QuantumTheory.Transport.Models.MassiveDirac

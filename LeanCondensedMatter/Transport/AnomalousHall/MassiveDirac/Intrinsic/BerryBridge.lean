import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband

set_option linter.style.header false

/-!
# Force-matrix / Berry-curvature bridge for the massive Dirac model

The model layer owns the gauge-independent two-band force-matrix numerator and interband energy gap.
This file identifies their Hall combination with the closed massive-Dirac Berry-curvature benchmark.
For target band `n` and opposite band `m`,

```text
Im Tr(P_m vₓ P_n vᵧ) = -s m v² / E,
E_n - E_m = 2 s E,
```

so the two-band force-matrix curvature reduces to `-s m v² / (2 E³)`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- The real two-band force-matrix Berry-curvature expression obtained from the Hall component of
the generic formula `2 Im(Fˣ_mn Fʸ_nm)/(E_n-E_m)²` after using that the energy denominator is real. -/
def forceMatrixBerryCurvature (band : Band) (v m px py : ℝ) : ℝ :=
  2 * (forceMatrixTraceNumerator .x .y band v m px py).im /
    interbandEnergyGap band v m px py ^ 2

/-- The projector/force-matrix expression equals the closed massive-Dirac Berry curvature away
from the band degeneracy. -/
theorem forceMatrixBerryCurvature_eq_berryCurvature (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixBerryCurvature band v m px py = berryCurvature band v m px py := by
  rw [forceMatrixBerryCurvature, forceMatrixTraceNumerator_im band v m px py hE,
    interbandEnergyGap_eq]
  cases band <;>
    simp [berryCurvature_upper, berryCurvature_lower] <;>
    field_simp [hE]

/-- Upper-band force-matrix curvature reproduces `Ω₊ = -m v²/(2E³)`. -/
theorem forceMatrixBerryCurvature_upper (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixBerryCurvature .upper v m px py =
      -(m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  rw [forceMatrixBerryCurvature_eq_berryCurvature .upper v m px py hE]
  exact berryCurvature_upper v m px py

/-- Lower-band force-matrix curvature reproduces `Ω₋ = +m v²/(2E³)`. -/
theorem forceMatrixBerryCurvature_lower (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixBerryCurvature .lower v m px py =
      (m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  rw [forceMatrixBerryCurvature_eq_berryCurvature .lower v m px py hE]
  exact berryCurvature_lower v m px py

end

end AnomalousHall.MassiveDirac

import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral

set_option linter.style.header false

/-!
# Force-matrix / Berry-curvature bridge for the massive Dirac model

This file evaluates the clean two-band force-matrix numerator without choosing eigenvector gauges.
For a target band `n` and the opposite band `m`, the rank-one spectral-projector identity

```text
Tr(P_m v_μ P_n v_ν) = ⟨m|v_μ|n⟩ ⟨n|v_ν|m⟩
```

identifies the direction-indexed projector trace with the interband numerator appearing in the
generic pointwise Berry-curvature formula of `Analysis.Operator.Spectral.BerryCurvature`.

For the Hall component `(μ,ν) = (x,y)`, the massive-Dirac projector algebra gives

```text
Im Tr(P_m vₓ P_n vᵧ) = -s m v² / E,
E_n - E_m = 2 s E,
```

so the two-band force-matrix curvature reduces to `-s m v² / (2 E³)`, exactly the closed
Berry-curvature benchmark already fixed in `MassiveDirac.lean`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- The other band in the two-band massive-Dirac model. -/
def oppositeBand : Band → Band
  | .lower => .upper
  | .upper => .lower

@[simp] theorem oppositeBand_lower : oppositeBand .lower = .upper := rfl
@[simp] theorem oppositeBand_upper : oppositeBand .upper = .lower := rfl
@[simp] theorem oppositeBand_oppositeBand (band : Band) : oppositeBand (oppositeBand band) = band := by
  cases band <;> rfl

/-- Energy denominator `E_n - E_m` with `m` the opposite band. -/
def interbandEnergyGap (band : Band) (v m px py : ℝ) : ℝ :=
  bandEnergy band v m px py - bandEnergy (oppositeBand band) v m px py

/-- In a two-band Dirac spectrum, the interband denominator is `2 s E`. -/
theorem interbandEnergyGap_eq (band : Band) (v m px py : ℝ) :
    interbandEnergyGap band v m px py = 2 * bandSign band * energy v m px py := by
  cases band <;> simp [interbandEnergyGap, bandEnergy] <;> ring

/-- Gauge-independent direction-indexed interband force-matrix numerator.

For rank-one spectral projectors this trace equals
`⟨m|v_μ|n⟩ ⟨n|v_ν|m⟩`, with `m = oppositeBand n`. -/
def forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (v m px py : ℝ) : ℂ :=
  Matrix.trace
    (bandProjector (oppositeBand band) v m px py * velocity μ v *
      bandProjector band v m px py * velocity ν v)

/-- The imaginary part of the massive-Dirac Hall force numerator is `-s m v²/E`. -/
theorem forceMatrixTraceNumerator_im (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    (forceMatrixTraceNumerator .x .y band v m px py).im =
      -(bandSign band) * m * v ^ 2 / energy v m px py := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  cases band <;>
    simp [forceMatrixTraceNumerator, oppositeBand, bandProjector, Matrix.trace, Matrix.mul_apply,
      velocity, directionPauli, hamiltonian, sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf

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

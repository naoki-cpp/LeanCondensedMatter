import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband

set_option linter.style.header false

/-!
# Force-matrix / Berry-curvature bridge for the massive Dirac model

The model layer owns the gauge-independent two-band force-matrix numerator and interband energy gap.
Their raw antisymmetrization in an ordered pair of in-plane directions is the natural oriented
Berry-curvature component. Here antisymmetrization means `F_μν - F_νμ`, with no factor of `1/2`;
the familiar two-dimensional scalar Berry curvature is the `(x,y)` component of that object.

For target band `n` and opposite band `m`,

```text
Im (F_xy - F_yx) = -2 s m v² / E,
E_n - E_m = 2 s E,
```

so the oriented `(x,y)` component reduces to `-s m v² / (2 E³)`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Oriented two-band Berry-curvature component obtained from the force-matrix trace numerator
antisymmetrization for an ordered in-plane direction pair. -/
def forceMatrixBerryCurvatureComponent
    (μ ν : Direction2) (band : Band) (v m px py : ℝ) : ℝ :=
  (forceMatrixTraceNumeratorAntisymmetrization μ ν band v m px py).im /
    interbandEnergyGap band v m px py ^ 2

/-- Exchanging the two in-plane directions reverses the oriented Berry-curvature component. -/
theorem forceMatrixBerryCurvatureComponent_swap
    (μ ν : Direction2) (band : Band) (v m px py : ℝ) :
    forceMatrixBerryCurvatureComponent ν μ band v m px py =
      -forceMatrixBerryCurvatureComponent μ ν band v m px py := by
  unfold forceMatrixBerryCurvatureComponent forceMatrixTraceNumeratorAntisymmetrization
  rw [swapDifference_swap, Complex.neg_im]
  ring

/-- The oriented Berry-curvature component vanishes on equal directions. -/
@[simp] theorem forceMatrixBerryCurvatureComponent_self
    (μ : Direction2) (band : Band) (v m px py : ℝ) :
    forceMatrixBerryCurvatureComponent μ μ band v m px py = 0 := by
  simp [forceMatrixBerryCurvatureComponent, forceMatrixTraceNumeratorAntisymmetrization]

/-- Two-dimensional scalar Berry curvature is the positively oriented `(x,y)` component. -/
def forceMatrixBerryCurvature (band : Band) (v m px py : ℝ) : ℝ :=
  forceMatrixBerryCurvatureComponent .x .y band v m px py

/-- The oriented `(x,y)` projector/force-matrix component equals the closed massive-Dirac Berry
curvature away from the band degeneracy. -/
theorem forceMatrixBerryCurvature_eq_berryCurvature (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixBerryCurvature band v m px py = berryCurvature band v m px py := by
  rw [forceMatrixBerryCurvature, forceMatrixBerryCurvatureComponent,
    forceMatrixTraceNumeratorAntisymmetrization_xy_im band v m px py hE,
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

end QuantumTheory.Transport.Models.MassiveDirac

import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral

set_option linter.style.header false

/-!
# Interband spectral algebra for the two-dimensional massive Dirac model

This file owns model-level interband relations shared by intrinsic and response calculations:
the interband energy gap, the gauge-independent projector/velocity trace, and its antisymmetric
exchange in the two in-plane directions. The two-band `oppositeBand` involution itself is basic
model data and is owned by `Model.Basic`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Energy denominator `E_n - E_m` with `m` the opposite band. -/
def interbandEnergyGap (band : Band) (v m px py : ℝ) : ℝ :=
  bandEnergy band v m px py - bandEnergy (oppositeBand band) v m px py

/-- In a two-band Dirac spectrum, the interband denominator is `2 s E`. -/
theorem interbandEnergyGap_eq (band : Band) (v m px py : ℝ) :
    interbandEnergyGap band v m px py = 2 * bandSign band * energy v m px py := by
  cases band <;> simp [interbandEnergyGap, bandEnergy] <;> ring

/-- Exchanging the two bands reverses the interband energy denominator. -/
@[simp] theorem interbandEnergyGap_oppositeBand
    (band : Band) (v m px py : ℝ) :
    interbandEnergyGap (oppositeBand band) v m px py =
      -interbandEnergyGap band v m px py := by
  rw [interbandEnergyGap_eq, interbandEnergyGap_eq, bandSign_oppositeBand]
  ring

/-- Away from the Dirac degeneracy, the interband energy gap is nonzero. -/
theorem interbandEnergyGap_ne_zero_of_energy_ne_zero
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    interbandEnergyGap band v m px py ≠ 0 := by
  rw [interbandEnergyGap_eq]
  cases band <;> simp [hE]

/-- Away from the Dirac degeneracy, the two band energies are distinct. -/
theorem bandEnergy_ne_oppositeBandEnergy
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandEnergy band v m px py ≠ bandEnergy (oppositeBand band) v m px py := by
  exact sub_ne_zero.mp (by
    simpa [interbandEnergyGap] using
      interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE)

/-- Gauge-independent direction-indexed interband force-matrix numerator.

For rank-one spectral projectors this trace equals
`⟨m|v_μ|n⟩ ⟨n|v_ν|m⟩`, with `m = oppositeBand n`. -/
def forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (v m px py : ℝ) : ℂ :=
  Matrix.trace
    (bandProjector (oppositeBand band) v m px py * velocity μ v *
      bandProjector band v m px py * velocity ν v)

/-- Antisymmetrization of the direction-indexed interband force-matrix numerator. -/
def forceMatrixAntisymmetricNumerator
    (μ ν : Direction2) (band : Band) (v m px py : ℝ) : ℂ :=
  forceMatrixTraceNumerator μ ν band v m px py -
    forceMatrixTraceNumerator ν μ band v m px py

/-- Exchanging the two current directions reverses the force-matrix antisymmetrization. -/
@[simp] theorem forceMatrixAntisymmetricNumerator_swap
    (μ ν : Direction2) (band : Band) (v m px py : ℝ) :
    forceMatrixAntisymmetricNumerator ν μ band v m px py =
      -forceMatrixAntisymmetricNumerator μ ν band v m px py := by
  unfold forceMatrixAntisymmetricNumerator
  ring

/-- The force-matrix antisymmetrization vanishes on equal directions. -/
@[simp] theorem forceMatrixAntisymmetricNumerator_self
    (μ : Direction2) (band : Band) (v m px py : ℝ) :
    forceMatrixAntisymmetricNumerator μ μ band v m px py = 0 := by
  simp [forceMatrixAntisymmetricNumerator]

/-- The oriented `(x,y)` force-matrix numerator is `-2 s m v²/E` in imaginary part. -/
theorem forceMatrixAntisymmetricNumerator_xy_im
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (forceMatrixAntisymmetricNumerator .x .y band v m px py).im =
      -2 * bandSign band * m * v ^ 2 / energy v m px py := by
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  cases band <;>
    simp [forceMatrixAntisymmetricNumerator, forceMatrixTraceNumerator, oppositeBand,
      bandProjector, Matrix.trace, Matrix.mul_apply, velocity, directionPauli, hamiltonian,
      sigmaX, sigmaY, sigmaZ] <;>
    field_simp [hEc] <;>
    ring_nf

end

end QuantumTheory.Transport.Models.MassiveDirac

import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral

set_option linter.style.header false

/-!
# Interband spectral algebra for the two-dimensional massive Dirac model

This file owns the model-level two-band relations shared by intrinsic and response calculations:
the opposite-band involution, the interband energy gap, and the gauge-independent projector/velocity
trace. These are consequences of the massive-Dirac spectrum and spectral projectors rather than of
a particular response representation.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

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

/-- Exchanging the two bands reverses the interband energy denominator. -/
@[simp] theorem interbandEnergyGap_oppositeBand
    (band : Band) (v m px py : ℝ) :
    interbandEnergyGap (oppositeBand band) v m px py =
      -interbandEnergyGap band v m px py := by
  rw [interbandEnergyGap_eq, interbandEnergyGap_eq]
  cases band <;> simp [oppositeBand, bandSign]

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

end

end QuantumTheory.Transport.Models.MassiveDirac

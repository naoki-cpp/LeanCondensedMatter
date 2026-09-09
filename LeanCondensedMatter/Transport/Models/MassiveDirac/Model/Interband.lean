import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral

set_option linter.style.header false

/-!
# Interband spectral algebra for the two-dimensional massive Dirac model

This file owns model-level interband relations shared by intrinsic and response calculations:
the interband energy gap and the gauge-independent projector/velocity trace. The two-band
`oppositeBand` involution itself is basic model data and is owned by `Model.Basic`.
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

/-- Exact complex `x-y` interband force numerator. The symmetric term is the in-plane product,
while the antisymmetric imaginary term is the mass component of the normalized Pauli vector. -/
theorem forceMatrixTraceNumerator_xy_eq (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixTraceNumerator .x .y band v m px py =
      -(((v ^ 4 * px * py / energy v m px py ^ 2 : ℝ) : ℂ)) -
        (((bandSign band * m * v ^ 2 / energy v m px py : ℝ) : ℂ)) * Complex.I := by
  let u : PauliAxis → ℂ :=
    (((bandSign band / energy v m px py : ℝ) : ℂ)) •
      diracPauliCoefficients v m px py
  have hProjector :
      bandProjector band v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) + InternalSpace.pauliCombination u) := by
    simp only [bandProjector, u, hamiltonian_eq_pauliCombination]
    rw [InternalSpace.pauliCombination_smul]
  have hOppositeProjector :
      bandProjector (oppositeBand band) v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) - InternalSpace.pauliCombination u) := by
    simp only [bandProjector, u, hamiltonian_eq_pauliCombination]
    rw [InternalSpace.pauliCombination_smul]
    simp [bandSign_oppositeBand]
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  unfold forceMatrixTraceNumerator
  rw [hOppositeProjector, hProjector]
  simp only [velocity, directionPauli]
  rw [InternalSpace.trace_halfIdentity_sub_pauliCombination_mul_scaledPauliX_mul_halfIdentity_add_pauliCombination_mul_scaledPauliY]
  cases band <;>
    simp [u, diracPauliCoefficients, bandSign] <;>
    field_simp [hEc] <;>
    ring

end

end QuantumTheory.Transport.Models.MassiveDirac

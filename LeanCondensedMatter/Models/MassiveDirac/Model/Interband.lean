import LeanCondensedMatter.Models.MassiveDirac.Model.Spectral

set_option linter.style.header false

/-!
# Interband spectral algebra for the two-dimensional massive Dirac model

This file owns model-level interband relations shared by intrinsic and response calculations:
the interband energy gap and the gauge-independent projector/velocity trace. The two-band
`oppositeBand` involution itself is basic model data and is owned by `Model.Basic`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section


/-- Energy denominator `E_n - E_m` with `m` the opposite band. -/
def interbandEnergyGap (band : Band) (v m px py : ℝ) : ℝ :=
  bandEnergy band v m px py - bandEnergy (oppositeBand band) v m px py

/-- In a two-band Dirac spectrum, the interband denominator is `2 s E`. -/
theorem interbandEnergyGap_eq (band : Band) (v m px py : ℝ) :
    interbandEnergyGap band v m px py = 2 * bandSign band * energy v m px py := by
  unfold interbandEnergyGap bandEnergy
  rw [bandSign_oppositeBand]
  ring

/-- Exchanging the two bands reverses the interband energy denominator. -/
@[simp] theorem interbandEnergyGap_oppositeBand
    (band : Band) (v m px py : ℝ) :
    interbandEnergyGap (oppositeBand band) v m px py =
      -interbandEnergyGap band v m px py := by
  simp only [interbandEnergyGap, oppositeBand_oppositeBand, neg_sub]

/-- The absolute interband gap is bounded below by `2|m|`, uniformly in momentum. -/
theorem two_mul_abs_mass_le_abs_interbandEnergyGap
    (band : Band) (v m px py : ℝ) :
    2 * |m| ≤ |interbandEnergyGap band v m px py| := by
  rw [interbandEnergyGap_eq]
  have hE := energy_nonneg v m px py
  have hmE := abs_mass_le_energy v m px py
  cases band <;> simp [bandSign, abs_of_nonneg hE] <;> linarith

/-- A pole window narrower than the mass gap is valid simultaneously at every momentum. -/
theorem radius_lt_abs_interbandEnergyGap_of_lt_two_mul_abs_mass
    (band : Band) (v m px py radius : ℝ)
    (hradius : radius < 2 * |m|) :
    radius < |interbandEnergyGap band v m px py| := by
  exact lt_of_lt_of_le hradius
    (two_mul_abs_mass_le_abs_interbandEnergyGap band v m px py)

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
  apply (bandEnergy_injective v m px py hE).ne
  cases band <;> decide

/-- Gauge-independent direction-indexed interband force-matrix numerator.

For rank-one spectral projectors this trace equals
`⟨m|v_μ|n⟩ ⟨n|v_ν|m⟩`, with `m = oppositeBand n`. -/
def forceMatrixTraceNumerator
    (μ ν : Fin 2) (band : Band) (v m px py : ℝ) : ℂ :=
  Matrix.trace
    (bandProjector (oppositeBand band) v m px py * velocity μ v *
      bandProjector band v m px py * velocity ν v)

/-- Exact complex `x-y` interband force numerator. The symmetric term is the in-plane product,
while the antisymmetric imaginary term is the mass component of the normalized Pauli vector. -/
theorem forceMatrixTraceNumerator_xy_eq (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixTraceNumerator 0 1 band v m px py =
      -(((v ^ 4 * px * py / energy v m px py ^ 2 : ℝ) : ℂ)) -
        (((bandSign band * m * v ^ 2 / energy v m px py : ℝ) : ℂ)) * Complex.I := by
  let u : PauliAxis → ℂ :=
    (((bandSign band / energy v m px py : ℝ) : ℂ)) •
      diracPauliCoefficients v m px py
  have hProjector :
      bandProjector band v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) + InternalSpace.pauliCombination u) := by
    simpa only [u] using bandProjector_eq_pauliCombination band v m px py
  have hOppositeProjector :
      bandProjector (oppositeBand band) v m px py =
        (1 / 2 : ℂ) • ((1 : Matrix2) - InternalSpace.pauliCombination u) := by
    calc
      _ = 1 - bandProjector band v m px py :=
        eq_sub_of_add_eq' (bandProjector_add_oppositeBand band v m px py)
      _ = _ := by rw [hProjector]; module
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  unfold forceMatrixTraceNumerator
  rw [hOppositeProjector, hProjector]
  change Matrix.trace
      (((1 / 2 : ℂ) • ((1 : Matrix2) - InternalSpace.pauliCombination u)) *
        (((v : ℝ) : ℂ) • sigmaX) *
        ((1 / 2 : ℂ) • ((1 : Matrix2) + InternalSpace.pauliCombination u)) *
        (((v : ℝ) : ℂ) • sigmaY)) = _
  rw [show sigmaX = InternalSpace.pauliX by rfl,
    show sigmaY = InternalSpace.pauliY by rfl,
    InternalSpace.trace_oppositePauliProjectors_xy]
  cases band <;>
    simp [u, diracPauliCoefficients, bandSign] <;>
    field_simp [hEc]

end

end QuantumTheory.Models.MassiveDirac

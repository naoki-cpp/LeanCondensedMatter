import LeanCondensedMatter.Models.RashbaExchange.Model.Spectral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Interband spectral algebra for the Rashba-exchange model

This module isolates the energy gap and gauge-independent interband velocity trace used by the
Berry and Bastin Hall channels.  The scalar parabolic dispersion shifts both bands and contributes
identity pieces to the velocities; the exact interband trace below proves that those pieces cancel
from the Hall numerator.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport

/-- Energy denominator between one band and its opposite partner. -/
def interbandEnergyGap
    (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  bandEnergy params band px py -
    bandEnergy params (oppositeBand band) px py

/-- The scalar kinetic shift cancels from the interband gap. -/
theorem interbandEnergyGap_eq
    (params : Parameters) (band : Band) (px py : ℝ) :
    interbandEnergyGap params band px py =
      2 * bandSign band * spinOrbitEnergy params px py := by
  cases band <;>
    simp [interbandEnergyGap, bandEnergy, bandSign] <;> ring

@[simp] theorem interbandEnergyGap_oppositeBand
    (params : Parameters) (band : Band) (px py : ℝ) :
    interbandEnergyGap params (oppositeBand band) px py =
      -interbandEnergyGap params band px py := by
  rw [interbandEnergyGap_eq, interbandEnergyGap_eq, bandSign_oppositeBand]
  ring

theorem interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    interbandEnergyGap params band px py ≠ 0 := by
  rw [interbandEnergyGap_eq]
  cases band <;> simp [bandSign, hE]

theorem bandEnergy_ne_oppositeBandEnergy
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    bandEnergy params band px py ≠
      bandEnergy params (oppositeBand band) px py := by
  exact sub_ne_zero.mp (by
    simpa [interbandEnergyGap] using
      interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero
        params band px py hE)

/-- Gauge-independent interband velocity numerator
`Tr(P_op v_μ P_band v_ν)`. -/
def forceMatrixTraceNumerator
    (params : Parameters) (μ ν : Fin 2) (band : Band) (px py : ℝ) : ℂ :=
  Matrix.trace
    (bandProjector params (oppositeBand band) px py *
      velocityOperator params μ px py *
      bandProjector params band px py *
      velocityOperator params ν px py)

/-- Exact x-y interband velocity trace.  The terms proportional to `p_i/m_eff I` cancel once the
projectors are nondegenerate, leaving only the Rashba/exchange Pauli geometry. -/
theorem forceMatrixTraceNumerator_xy_eq
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    forceMatrixTraceNumerator params 0 1 band px py =
      -(((params.rashbaVelocity ^ 4 * px * py /
          spinOrbitEnergy params px py ^ 2 : ℝ) : ℂ)) -
        (((bandSign band * params.exchangeSplitting *
          params.rashbaVelocity ^ 2 / spinOrbitEnergy params px py : ℝ) : ℂ)) *
          Complex.I := by
  let u : InternalSpace.PauliAxis → ℂ :=
    (((bandSign band / spinOrbitEnergy params px py : ℝ) : ℂ)) •
      rashbaPauliCoefficients params px py
  have hProjector :
      bandProjector params band px py =
        (1 / 2 : ℂ) •
          ((1 : InternalSpace.PauliMatrix) + InternalSpace.pauliCombination u) := by
    simpa only [u] using bandProjector_eq_pauliCombination params band px py
  have hOppositeProjector :
      bandProjector params (oppositeBand band) px py =
        (1 / 2 : ℂ) •
          ((1 : InternalSpace.PauliMatrix) - InternalSpace.pauliCombination u) := by
    have hresolve := bandProjector_add_oppositeBand params band px py
    rw [hProjector] at hresolve
    have hsub :
        bandProjector params (oppositeBand band) px py =
          1 - (1 / 2 : ℂ) •
            ((1 : InternalSpace.PauliMatrix) + InternalSpace.pauliCombination u) := by
      apply (eq_sub_iff_add_eq).2
      simpa [add_comm] using hresolve
    rw [hsub]
    module
  have hEc : (((spinOrbitEnergy params px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hnorm : dotProduct u u = 1 := by
    rw [InternalSpace.dotProduct_pauliAxis]
    simp [u, rashbaPauliCoefficients]
    have hsq := spinOrbitEnergy_sq params px py
    unfold spinOrbitEnergySq momentumSq2D at hsq
    field_simp [hEc]
    have hreal :
        bandSign band ^ 2 *
            (params.rashbaVelocity ^ 2 * (py ^ 2 + px ^ 2) +
              params.exchangeSplitting ^ 2) =
          spinOrbitEnergy params px py ^ 2 := by
      rw [bandSign_sq, hsq]
      ring
    exact_mod_cast hreal
  have htrace
      (u : InternalSpace.PauliAxis → ℂ) (cx cy a : ℂ)
      (hnorm : dotProduct u u = 1) :
      Matrix.trace
          (((1 / 2 : ℂ) •
              ((1 : InternalSpace.PauliMatrix) - InternalSpace.pauliCombination u)) *
            (cx • (1 : InternalSpace.PauliMatrix) - a • InternalSpace.pauliY) *
            ((1 / 2 : ℂ) •
              ((1 : InternalSpace.PauliMatrix) + InternalSpace.pauliCombination u)) *
            (cy • (1 : InternalSpace.PauliMatrix) + a • InternalSpace.pauliX)) =
        a ^ 2 * (u .x * u .y) - Complex.I * a ^ 2 * u .z := by
    have hI : Complex.I ^ 2 = (-1 : ℂ) := by
      simpa [pow_two] using Complex.I_mul_I
    rw [InternalSpace.dotProduct_pauliAxis] at hnorm
    simp [Matrix.trace, Matrix.mul_apply, InternalSpace.pauliCombination_eq_components,
      InternalSpace.pauliX, InternalSpace.pauliY, InternalSpace.pauliZ,
      sub_eq_add_neg]
    ring_nf
    simp [hI]
    ring_nf at hnorm
    linear_combination -(cx * cy / 2) * hnorm
  unfold forceMatrixTraceNumerator
  rw [hOppositeProjector, hProjector]
  change Matrix.trace
      (((1 / 2 : ℂ) •
          ((1 : InternalSpace.PauliMatrix) - InternalSpace.pauliCombination u)) *
        ((((px / params.effectiveMass : ℝ) : ℂ)) •
          (1 : InternalSpace.PauliMatrix) -
          ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliY) *
        ((1 / 2 : ℂ) •
          ((1 : InternalSpace.PauliMatrix) + InternalSpace.pauliCombination u)) *
        ((((py / params.effectiveMass : ℝ) : ℂ)) •
          (1 : InternalSpace.PauliMatrix) +
          ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliX)) = _
  rw [htrace u
    (((px / params.effectiveMass : ℝ) : ℂ))
    (((py / params.effectiveMass : ℝ) : ℂ))
    (((params.rashbaVelocity : ℝ) : ℂ)) hnorm]
  cases band <;>
    simp [u, rashbaPauliCoefficients, bandSign] <;>
    field_simp [hEc]

/-- The force-matrix expression for the x-y Berry curvature. -/
def forceMatrixBerryCurvature
    (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  2 * (forceMatrixTraceNumerator params 0 1 band px py).im /
    interbandEnergyGap params band px py ^ 2

/-- The gauge-independent force-matrix curvature equals the model's closed Berry-curvature formula
away from the band degeneracy. -/
theorem forceMatrixBerryCurvature_eq_berryCurvature
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    forceMatrixBerryCurvature params band px py =
      berryCurvature params band px py := by
  rw [forceMatrixBerryCurvature,
    forceMatrixTraceNumerator_xy_eq params band px py hE,
    interbandEnergyGap_eq]
  simp only [Complex.sub_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  cases band <;>
    simp [berryCurvature, bandSign] <;>
    field_simp [hE]

end

end QuantumTheory.Models.RashbaExchange

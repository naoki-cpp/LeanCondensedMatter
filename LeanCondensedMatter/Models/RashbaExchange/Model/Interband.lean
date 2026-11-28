import LeanCondensedMatter.Models.RashbaExchange.Model.Spectral
import LeanCondensedMatter.Analysis.Operator.BerryGeometry
import LeanCondensedMatter.QuantumTheory.TwoBand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Interband spectral algebra for the Rashba-exchange model

This module isolates the clean energy gap and gauge-independent interband velocity trace used by
Berry and Bastin Hall calculations. These definitions require only `HamiltonianParameters`.
The scalar parabolic dispersion shifts both bands and contributes identity pieces to the
velocities; the exact interband trace below proves that those pieces cancel from the Hall numerator.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.TwoBand

noncomputable section

/-- Energy denominator between one band and its opposite partner. -/
def interbandEnergyGap
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) : ℝ :=
  bandEnergy params band px py -
    bandEnergy params (oppositeBand band) px py

/-- The scalar kinetic shift cancels from the interband gap. -/
theorem interbandEnergyGap_eq
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
    interbandEnergyGap params band px py =
      2 * bandSign band * spinOrbitEnergy params px py := by
  exact TwoBand.shiftedEnergy_sub_oppositeBand band
    (kineticEnergy params px py) (spinOrbitEnergy params px py)

@[simp] theorem interbandEnergyGap_oppositeBand
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
    interbandEnergyGap params (oppositeBand band) px py =
      -interbandEnergyGap params band px py := by
  simp only [interbandEnergyGap, oppositeBand_oppositeBand, neg_sub]

theorem interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    interbandEnergyGap params band px py ≠ 0 := by
  rw [interbandEnergyGap_eq]
  cases band <;> simp [bandSign, hE]

theorem bandEnergy_ne_oppositeBandEnergy
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    bandEnergy params band px py ≠
      bandEnergy params (oppositeBand band) px py := by
  apply (bandEnergy_injective params px py hE).ne
  exact TwoBand.ne_oppositeBand band

/-- Gauge-independent interband velocity numerator
`Tr(P_op v_μ P_band v_ν)`. -/
def forceMatrixTraceNumerator
    (params : HamiltonianParameters) (μ ν : Fin 2) (band : TwoBand) (px py : ℝ) : ℂ :=
  Matrix.trace
    (bandProjector params (oppositeBand band) px py *
      velocityOperator params μ px py *
      bandProjector params band px py *
      velocityOperator params ν px py)

/-- Exact x-y interband velocity trace.  The terms proportional to `p_i/m_eff I` cancel once the
projectors are nondegenerate, leaving only the Rashba/exchange Pauli geometry. -/
theorem forceMatrixTraceNumerator_xy_eq
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
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
    rw [eq_sub_of_add_eq' (bandProjector_add_oppositeBand params band px py), hProjector]
    module
  have hEc : (((spinOrbitEnergy params px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have hnorm : dotProduct u u = 1 := by
    dsimp only [u]
    rw [smul_dotProduct, dotProduct_smul, rashbaPauliCoefficients_dot_self,
      ← spinOrbitEnergy_sq, Complex.ofReal_pow]
    simp only [smul_eq_mul, Complex.ofReal_div]
    cases band <;> simp [bandSign] <;> field_simp [hEc]
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
  let x : InternalSpace.PauliAxis → ℂ := fun axis =>
    InternalSpace.pauliAxisComponent axis 0 (-(params.rashbaVelocity : ℂ)) 0
  let y : InternalSpace.PauliAxis → ℂ := fun axis =>
    InternalSpace.pauliAxisComponent axis (params.rashbaVelocity : ℂ) 0 0
  have hx : InternalSpace.pauliCombination x = -((params.rashbaVelocity : ℂ) •
      InternalSpace.pauliY) := by
    simp [x, InternalSpace.pauliCombination_eq_components, InternalSpace.pauliAxisComponent]
  have hy : InternalSpace.pauliCombination y = (params.rashbaVelocity : ℂ) •
      InternalSpace.pauliX := by
    simp [y, InternalSpace.pauliCombination_eq_components, InternalSpace.pauliAxisComponent]
  have h := InternalSpace.trace_oppositePauliProjectors u x y
    ((px / params.effectiveMass : ℝ) : ℂ) ((py / params.effectiveMass : ℝ) : ℂ)
  simp only [hx, hy, ← sub_eq_add_neg] at h
  rw [h, hnorm]
  simp [x, y, InternalSpace.dotProduct_pauliAxis, InternalSpace.pauliCross,
    cross_apply, InternalSpace.pauliAxisComponent, u, rashbaPauliCoefficients]
  cases band <;> simp [bandSign] <;> field_simp [hEc]

/-- The force-matrix expression for the x-y Berry curvature. -/
def forceMatrixBerryCurvature
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) : ℝ :=
  2 * (forceMatrixTraceNumerator params 0 1 band px py).im /
    interbandEnergyGap params band px py ^ 2

/-- The gauge-independent force-matrix curvature equals the model's closed Berry-curvature formula
away from the band degeneracy. -/
theorem forceMatrixBerryCurvature_eq_berryCurvature
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    forceMatrixBerryCurvature params band px py =
      berryCurvature params band px py := by
  rw [forceMatrixBerryCurvature,
    forceMatrixTraceNumerator_xy_eq params band px py hE,
    interbandEnergyGap_eq]
  simpa only [berryCurvature, Complex.ofReal_neg, mul_assoc] using
    (BerryGeometry.signedInterbandBerryWeight_eq
      (-(params.rashbaVelocity ^ 4 * px * py / spinOrbitEnergy params px py ^ 2))
      (bandSign band) (spinOrbitEnergy params px py)
      (params.exchangeSplitting * params.rashbaVelocity ^ 2) (bandSign_sq band) hE)

end

end QuantumTheory.Models.RashbaExchange

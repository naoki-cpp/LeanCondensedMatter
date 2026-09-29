import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Bands
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Interband Bastin block antisymmetry for the Rashba-exchange model

The antisymmetric interband current block is normalized by the squared two-band gap and identified
exactly with the closed Rashba-exchange Berry curvature.  This remains pointwise in momentum and
does not perform an energy integral or zero-broadening limit.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

/-- Antisymmetric direction exchange of the interband Bastin block at a selected target band. -/
noncomputable def bastinInterbandBlockDifference
    (params : Parameters) (μ ν : Fin 2) (band : Band) (px py : ℝ) : ℂ :=
  bastinBandBlockTrace params μ ν (oppositeBand band) band px py -
    bastinBandBlockTrace params ν μ (oppositeBand band) band px py

theorem bastinInterbandBlockDifference_swap
    (params : Parameters) (μ ν : Fin 2) (band : Band) (px py : ℝ) :
    bastinInterbandBlockDifference params ν μ band px py =
      -bastinInterbandBlockDifference params μ ν band px py := by
  unfold bastinInterbandBlockDifference
  ring

@[simp] theorem bastinInterbandBlockDifference_self
    (params : Parameters) (μ : Fin 2) (band : Band) (px py : ℝ) :
    bastinInterbandBlockDifference params μ μ band px py = 0 := by
  simp [bastinInterbandBlockDifference]

/-- The normalized x-y interband Bastin block is `-q² Ω_band`. -/
theorem bastinInterbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    (bastinInterbandBlockDifference params 0 1 band px py).im /
        interbandEnergyGap params band px py ^ 2 =
      -(params.signedCharge ^ 2 * berryCurvature params band px py) := by
  have hband :=
    two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
      params band px py hE
  have hopp :=
    two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
      params (oppositeBand band) px py hE
  rw [interbandEnergyGap_oppositeBand, berryCurvature_oppositeBand] at hopp
  simp [pow_two] at hopp
  unfold bastinInterbandBlockDifference
  rw [bastinBandBlockTrace_swap params 0 1 (oppositeBand band) band]
  rw [bastinBandBlockTrace_eq_currentBandBlockTrace
      params 0 1 (oppositeBand band) band,
    bastinBandBlockTrace_eq_currentBandBlockTrace
      params 0 1 band (oppositeBand band),
    Complex.sub_im]
  have hgap :=
    interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero
      params band px py hE
  field_simp [hgap] at hband hopp ⊢
  nlinarith

end

end QuantumTheory.Transport.Models.RashbaExchange

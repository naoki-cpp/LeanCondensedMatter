import LeanCondensedMatter.Transport.Disorder.TraceNormBound
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite-dimensional error bound against an arbitrary supplied dressed RA trace

The exact quenched two-Green trace is compared to a supplied pair of Green operators and a
supplied dressed source vertex. The error is bounded by three distinct nonnegative terms:

1. left one-particle Green mismatch, with the exact right Green operator bounded by |γR|⁻¹;
2. right one-particle Green mismatch;
3. the difference between the exact connected insertion and the supplied vertex dressing.

Unlike the purely algebraic bridge, this yields a quantitative (dimension-explicit) norm bound.
It is conditional on control of the actual approximation residuals: no assertion that the
Born–Dyson or noncrossing-ladder candidates control them follows here. Same-side, sea,
contact, conductivity normalization and DC/zero-broadening limits remain separate.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [FiniteDimensional ℂ H] [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Explicit residual-norm stability of the finite-dimensional two-Green trace against
arbitrary supplied propagators and a dressed source vertex. This bounds the *actual*
connected-vertex mismatch, not the connected insertion alone. -/
theorem norm_averagedTwoGreenTrace_sub_dressed_le_residuals
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregRight : regulatorRight ≠ 0)
    (measuredVertex bareSourceVertex : H →L[ℂ] H)
    (suppliedLeftGreen dressedSourceVertex suppliedRightGreen : H →L[ℂ] H) :
    ‖ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight
        measuredVertex bareSourceVertex -
      retardedAdvancedVertexTraceKernel
        measuredVertex suppliedLeftGreen dressedSourceVertex suppliedRightGreen‖ ≤
      ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) *
        (‖ensemble.averagedGreenOfRegulator energyLeft regulatorLeft -
              suppliedLeftGreen‖ * ‖bareSourceVertex‖ * |regulatorRight|⁻¹ +
          ‖suppliedLeftGreen‖ * ‖bareSourceVertex‖ *
            ‖ensemble.averagedGreenOfRegulator energyRight regulatorRight -
              suppliedRightGreen‖ +
          ‖ensemble.connectedTwoGreenInsertionOfRegulators
                energyLeft regulatorLeft energyRight regulatorRight bareSourceVertex -
              suppliedLeftGreen * (dressedSourceVertex - bareSourceVertex) *
                suppliedRightGreen‖) := by
  let meanL := ensemble.averagedGreenOfRegulator energyLeft regulatorLeft
  let meanR := ensemble.averagedGreenOfRegulator energyRight regulatorRight
  let conn := ensemble.connectedTwoGreenInsertionOfRegulators
    energyLeft regulatorLeft energyRight regulatorRight bareSourceVertex
  let trace := ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H)
  let a := (meanL - suppliedLeftGreen) * bareSourceVertex * meanR
  let b := suppliedLeftGreen * bareSourceVertex * (meanR - suppliedRightGreen)
  let c := conn - suppliedLeftGreen * (dressedSourceVertex - bareSourceVertex) *
    suppliedRightGreen
  have hmeanR : ‖meanR‖ ≤ |regulatorRight|⁻¹ := by
    change ‖ensemble.average (fun ω =>
      ensemble.configurationGreenOfRegulator energyRight regulatorRight ω)‖ ≤ _
    apply ensemble.norm_average_le_of_forall _ _
    intro ω
    exact norm_resolvent_spectralParameterOfRegulator_le
      (ensemble.configurationHamiltonian ω).1
      (ensemble.configurationHamiltonian ω).2
      energyRight regulatorRight hregRight
  have ha :
      ‖a‖ ≤ ‖meanL - suppliedLeftGreen‖ * ‖bareSourceVertex‖ * |regulatorRight|⁻¹ := by
    calc
      ‖a‖ ≤ (‖meanL - suppliedLeftGreen‖ * ‖bareSourceVertex‖) * ‖meanR‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_mul_le (meanL - suppliedLeftGreen) bareSourceVertex)
            (norm_nonneg meanR))
      _ ≤ _ := mul_le_mul_of_nonneg_left hmeanR
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hb :
      ‖b‖ ≤ ‖suppliedLeftGreen‖ * ‖bareSourceVertex‖ *
        ‖meanR - suppliedRightGreen‖ := by
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (norm_mul_le suppliedLeftGreen bareSourceVertex)
        (norm_nonneg _))
  have hsum : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    calc
      ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (‖a‖ + ‖b‖) + ‖c‖ :=
        add_le_add_right (norm_add_le a b) _
  rw [ensemble.averagedTwoGreenVertexTraceKernelOfRegulators_sub_dressed_eq]
  change ‖trace (measuredVertex * (a + b + c))‖ ≤
    ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) *
      (‖meanL - suppliedLeftGreen‖ * ‖bareSourceVertex‖ * |regulatorRight|⁻¹ +
        ‖suppliedLeftGreen‖ * ‖bareSourceVertex‖ *
          ‖meanR - suppliedRightGreen‖ + ‖c‖)
  have hsum' :
      ‖a + b + c‖ ≤
        ‖meanL - suppliedLeftGreen‖ * ‖bareSourceVertex‖ * |regulatorRight|⁻¹ +
          ‖suppliedLeftGreen‖ * ‖bareSourceVertex‖ *
            ‖meanR - suppliedRightGreen‖ + ‖c‖ := by
    exact hsum.trans (add_le_add (add_le_add ha hb) le_rfl)
  calc
    ‖trace (measuredVertex * (a + b + c))‖ ≤
        (Module.finrank ℂ H : ℝ) * ‖measuredVertex * (a + b + c)‖ :=
      ContinuousLinearMap.norm_finiteDimensionalOperatorTrace_le_finrank_mul _
    _ ≤ (Module.finrank ℂ H : ℝ) *
        (‖measuredVertex‖ * ‖a + b + c‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Nat.cast_nonneg _)
    _ = ((Module.finrank ℂ H : ℝ) * ‖measuredVertex‖) * ‖a + b + c‖ := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum'
      (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport

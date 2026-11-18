import LeanCondensedMatter.Transport.Disorder.LadderNormBound
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Exact disorder covariance against a genuinely resummed finite Born ladder

Combine the cubic first-rung error from `FirstRungNormBound` with the geometric
bound on *all higher ladder rungs*. For a centered finite self-adjoint impurity
ensemble, `‖Vω‖ ≤ M`, and independent nonzero signed regulators, put

```text
B_L = |γL|⁻¹, B_R = |γR|⁻¹, q = M² B_L B_R.
```

If `q < 1`, the clean finite-ensemble ladder admits a resummed fixed point.
The exact connected two-Green covariance is within

```text
[4 B_L³ B_R² + 2 B_L² B_R³] M³ ‖J‖
    + B_L B_R [q²/(1-q)] ‖J‖
```

of its dressed-vertex insertion, with **all higher ladder rungs** controlled.
This does not identify the supplied continuum Born/SCBA dressed vertex with this
finite-ensemble ladder or provide a vanishing broadening / DC Hall theorem.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The exact connected insertion is close to the first Born rung **plus all
higher geometric ladder rungs**, with explicit microscopic smallness condition.
The `hinvertible` witness is always available under `hsmall` by
`isUnit_one_sub_freeGreenLadder_of_smallPotential`. -/
theorem norm_connectedTwoGreen_sub_resummedFreeLadder_le
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregLeft : regulatorLeft ≠ 0) (hregRight : regulatorRight ≠ 0)
    (hcentered : ensemble.IsCentered)
    (vertex : H →L[ℂ] H)
    (potentialBound : ℝ) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound)
    (hsmall : potentialBound ^ 2 * |regulatorLeft|⁻¹ *
        |regulatorRight|⁻¹ < 1)
    (hinvertible : IsUnit (1 - ensemble.retardedAdvancedLadderCLM
        (ensemble.freeGreenOfRegulator energyLeft regulatorLeft)
        (ensemble.freeGreenOfRegulator energyRight regulatorRight))) :
    ‖ensemble.connectedTwoGreenInsertionOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight vertex -
      ensemble.freeGreenOfRegulator energyLeft regulatorLeft *
        (resummedLadderVertex
          (ensemble.retardedAdvancedLadderCLM
            (ensemble.freeGreenOfRegulator energyLeft regulatorLeft)
            (ensemble.freeGreenOfRegulator energyRight regulatorRight))
          hinvertible vertex - vertex) *
        ensemble.freeGreenOfRegulator energyRight regulatorRight‖ ≤
      ((2 * (|regulatorLeft|⁻¹) ^ 3 * potentialBound ^ 2) *
          ‖vertex‖ * (2 * (|regulatorRight|⁻¹) ^ 2 * potentialBound) +
        ((|regulatorLeft|⁻¹) ^ 2 * potentialBound) * ‖vertex‖ *
          (2 * (|regulatorRight|⁻¹) ^ 3 * potentialBound ^ 2)) +
      (|regulatorLeft|⁻¹ * |regulatorRight|⁻¹) *
        ((potentialBound ^ 2 * |regulatorLeft|⁻¹ * |regulatorRight|⁻¹) ^ 2 /
          (1 - potentialBound ^ 2 * |regulatorLeft|⁻¹ * |regulatorRight|⁻¹) *
          ‖vertex‖) := by
  let freeLeft := ensemble.freeGreenOfRegulator energyLeft regulatorLeft
  let freeRight := ensemble.freeGreenOfRegulator energyRight regulatorRight
  let ladder := ensemble.retardedAdvancedLadderCLM freeLeft freeRight
  let dressed := resummedLadderVertex ladder hinvertible vertex
  let connected := ensemble.connectedTwoGreenInsertionOfRegulators
    energyLeft regulatorLeft energyRight regulatorRight vertex
  let firstRung := ensemble.firstBornTwoGreenRungOfRegulators
    energyLeft regulatorLeft energyRight regulatorRight vertex
  let leftBound : ℝ := |regulatorLeft|⁻¹
  let rightBound : ℝ := |regulatorRight|⁻¹
  let q : ℝ := potentialBound ^ 2 * leftBound * rightBound
  let cubic : ℝ :=
    (2 * leftBound ^ 3 * potentialBound ^ 2) * ‖vertex‖ *
        (2 * rightBound ^ 2 * potentialBound) +
      (leftBound ^ 2 * potentialBound) * ‖vertex‖ *
        (2 * rightBound ^ 3 * potentialBound ^ 2)
  have hleft : ‖freeLeft‖ ≤ leftBound :=
    norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energyLeft regulatorLeft hregLeft
  have hright : ‖freeRight‖ ≤ rightBound :=
    norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energyRight regulatorRight hregRight
  have hleftNonneg : 0 ≤ leftBound :=
    inv_nonneg.mpr (abs_nonneg regulatorLeft)
  have hrightNonneg : 0 ≤ rightBound :=
    inv_nonneg.mpr (abs_nonneg regulatorRight)
  have hq : ‖ladder‖ ≤ q :=
    ensemble.norm_freeGreenLadder_le_uniformPotential_sq
      energyLeft regulatorLeft energyRight regulatorRight
      hregLeft hregRight potentialBound hbound hpotential
  have htail : ‖ladder (dressed - vertex)‖ ≤
      q ^ 2 / (1 - q) * ‖vertex‖ :=
    norm_resummedLadderVertex_tail_le ladder hinvertible vertex q hq hsmall
  have htailNonneg : 0 ≤ q ^ 2 / (1 - q) * ‖vertex‖ := by
    apply mul_nonneg
    · exact div_nonneg (sq_nonneg q) (le_of_lt (sub_pos.mpr hsmall))
    · exact norm_nonneg vertex
  have hfirst :
      firstRung = freeLeft * ladder vertex * freeRight := rfl
  have hdecomp : dressed - vertex =
      ladder vertex + ladder (dressed - vertex) :=
    resummedLadderVertex_sub_eq_firstRung_add_tail ladder hinvertible vertex
  have hdiff :
      firstRung - freeLeft * (dressed - vertex) * freeRight =
        -(freeLeft * ladder (dressed - vertex) * freeRight) := by
    rw [hfirst]
    nth_rw 1 [hdecomp]
    noncomm_ring
  have htailSandwich :
      ‖firstRung - freeLeft * (dressed - vertex) * freeRight‖ ≤
        (leftBound * rightBound) * (q ^ 2 / (1 - q) * ‖vertex‖) := by
    rw [hdiff, norm_neg]
    calc
      ‖freeLeft * ladder (dressed - vertex) * freeRight‖ ≤
          ‖freeLeft‖ * ‖ladder (dressed - vertex)‖ * ‖freeRight‖ := by
        simpa only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil,
          mul_one, mul_assoc] using
          (List.norm_prod_le'
            (l := [freeLeft, ladder (dressed - vertex), freeRight]) (by simp))
      _ ≤ leftBound * ‖ladder (dressed - vertex)‖ * ‖freeRight‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hleft
            (norm_nonneg (ladder (dressed - vertex))))
          (norm_nonneg freeRight)
      _ ≤ leftBound * (q ^ 2 / (1 - q) * ‖vertex‖) * ‖freeRight‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htail hleftNonneg)
          (norm_nonneg freeRight)
      _ ≤ leftBound * (q ^ 2 / (1 - q) * ‖vertex‖) * rightBound := by
        exact mul_le_mul_of_nonneg_left hright
          (mul_nonneg hleftNonneg htailNonneg)
      _ = (leftBound * rightBound) * (q ^ 2 / (1 - q) * ‖vertex‖) := by ring
  have hcubic : ‖connected - firstRung‖ ≤ cubic :=
    ensemble.norm_connectedTwoGreen_sub_firstBornRung_le_cubic
      energyLeft regulatorLeft energyRight regulatorRight
      hregLeft hregRight hcentered vertex potentialBound hbound hpotential
  have hsplit :
      connected - freeLeft * (dressed - vertex) * freeRight =
        (connected - firstRung) +
          (firstRung - freeLeft * (dressed - vertex) * freeRight) := by abel
  change ‖connected - freeLeft * (dressed - vertex) * freeRight‖ ≤
    cubic + (leftBound * rightBound) * (q ^ 2 / (1 - q) * ‖vertex‖)
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hcubic htailSandwich)

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport
